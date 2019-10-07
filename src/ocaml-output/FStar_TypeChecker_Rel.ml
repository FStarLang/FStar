open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____46 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____81 -> false
  
let (__proj__UNIV__item___0 :
  uvi -> (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe))
  = fun projectee  -> match projectee with | UNIV _0 -> _0 
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs ;
  wl_deferred:
    (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list ;
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
    (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list)
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
                    let uu____504 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____504;
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
                     (let uu___71_536 = wl  in
                      {
                        attempting = (uu___71_536.attempting);
                        wl_deferred = (uu___71_536.wl_deferred);
                        ctr = (uu___71_536.ctr);
                        defer_ok = (uu___71_536.defer_ok);
                        smt_ok = (uu___71_536.smt_ok);
                        umax_heuristic_ok = (uu___71_536.umax_heuristic_ok);
                        tcenv = (uu___71_536.tcenv);
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
            let uu___77_569 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___77_569.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___77_569.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___77_569.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___77_569.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___77_569.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___77_569.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___77_569.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___77_569.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___77_569.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___77_569.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___77_569.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___77_569.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___77_569.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___77_569.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___77_569.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___77_569.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___77_569.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___77_569.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___77_569.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___77_569.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___77_569.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___77_569.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___77_569.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___77_569.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___77_569.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___77_569.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___77_569.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___77_569.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___77_569.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___77_569.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___77_569.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___77_569.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___77_569.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___77_569.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___77_569.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___77_569.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___77_569.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___77_569.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___77_569.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___77_569.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___77_569.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___77_569.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___77_569.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___77_569.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____571 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____571 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Common.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * Prims.string) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____614 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____650 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * Prims.string)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____683 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____694 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____705 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___0_723  ->
    match uu___0_723 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____735 = FStar_Syntax_Util.head_and_args t  in
    match uu____735 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____798 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____800 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____815 =
                     let uu____817 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____817  in
                   FStar_Util.format1 "@<%s>" uu____815
                in
             let uu____821 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____798 uu____800 uu____821
         | uu____824 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___1_836  ->
      match uu___1_836 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____841 =
            let uu____845 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____847 =
              let uu____851 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____853 =
                let uu____857 =
                  let uu____861 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____861]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____857
                 in
              uu____851 :: uu____853  in
            uu____845 :: uu____847  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____841
      | FStar_TypeChecker_Common.CProb p ->
          let uu____872 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____874 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____876 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____872 uu____874
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____876
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___2_890  ->
      match uu___2_890 with
      | UNIV (u,t) ->
          let x =
            let uu____896 = FStar_Options.hide_uvar_nums ()  in
            if uu____896
            then "?"
            else
              (let uu____903 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____903 FStar_Util.string_of_int)
             in
          let uu____907 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____907
      | TERM (u,t) ->
          let x =
            let uu____914 = FStar_Options.hide_uvar_nums ()  in
            if uu____914
            then "?"
            else
              (let uu____921 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____921 FStar_Util.string_of_int)
             in
          let uu____925 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____925
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____944 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____944 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____965 =
      let uu____969 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____969
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____965 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____988 .
    (FStar_Syntax_Syntax.term * 'Auu____988) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1007 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1028  ->
              match uu____1028 with
              | (x,uu____1035) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1007 (FStar_String.concat " ")
  
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
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1078 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1078
         then
           let uu____1083 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1083
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___3_1094  ->
    match uu___3_1094 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1100 .
    'Auu____1100 FStar_TypeChecker_Common.problem ->
      'Auu____1100 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___137_1112 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___137_1112.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___137_1112.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___137_1112.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___137_1112.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___137_1112.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___137_1112.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___137_1112.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1120 .
    'Auu____1120 FStar_TypeChecker_Common.problem ->
      'Auu____1120 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___4_1140  ->
    match uu___4_1140 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1146  -> FStar_TypeChecker_Common.TProb _1146)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1152  -> FStar_TypeChecker_Common.CProb _1152)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___5_1158  ->
    match uu___5_1158 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___149_1164 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___149_1164.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___149_1164.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___149_1164.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___149_1164.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___149_1164.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___149_1164.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___149_1164.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___149_1164.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___149_1164.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___153_1172 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___153_1172.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___153_1172.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___153_1172.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___153_1172.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___153_1172.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___153_1172.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___153_1172.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___153_1172.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___153_1172.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___6_1185  ->
      match uu___6_1185 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___7_1192  ->
    match uu___7_1192 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___8_1205  ->
    match uu___8_1205 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___9_1220  ->
    match uu___9_1220 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___10_1235  ->
    match uu___10_1235 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___11_1249  ->
    match uu___11_1249 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___12_1263  ->
    match uu___12_1263 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___13_1275  ->
    match uu___13_1275 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1291 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____1291) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1321 =
          let uu____1323 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1323  in
        if uu____1321
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1360)::bs ->
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
          let uu____1407 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1431 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1431]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1407
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1459 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1483 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1483]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1459
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1530 =
          let uu____1532 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1532  in
        if uu____1530
        then ()
        else
          (let uu____1537 =
             let uu____1540 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1540
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____1537 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____1589 =
          let uu____1591 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1591  in
        if uu____1589
        then ()
        else
          (let uu____1596 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____1596)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____1616 =
        let uu____1618 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____1618  in
      if uu____1616
      then ()
      else
        (let msgf m =
           let uu____1632 =
             let uu____1634 =
               let uu____1636 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____1636 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____1634  in
           Prims.op_Hat msg uu____1632  in
         (let uu____1641 = msgf "scope"  in
          let uu____1644 = p_scope prob  in
          def_scope_wf uu____1641 (p_loc prob) uu____1644);
         (let uu____1656 = msgf "guard"  in
          def_check_scoped uu____1656 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____1663 = msgf "lhs"  in
                def_check_scoped uu____1663 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1666 = msgf "rhs"  in
                def_check_scoped uu____1666 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____1673 = msgf "lhs"  in
                def_check_scoped_comp uu____1673 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1676 = msgf "rhs"  in
                def_check_scoped_comp uu____1676 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___246_1697 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___246_1697.wl_deferred);
          ctr = (uu___246_1697.ctr);
          defer_ok = (uu___246_1697.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___246_1697.umax_heuristic_ok);
          tcenv = (uu___246_1697.tcenv);
          wl_implicits = (uu___246_1697.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1705 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1705 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___250_1728 = empty_worklist env  in
      let uu____1729 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1729;
        wl_deferred = (uu___250_1728.wl_deferred);
        ctr = (uu___250_1728.ctr);
        defer_ok = (uu___250_1728.defer_ok);
        smt_ok = (uu___250_1728.smt_ok);
        umax_heuristic_ok = (uu___250_1728.umax_heuristic_ok);
        tcenv = (uu___250_1728.tcenv);
        wl_implicits = (uu___250_1728.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___255_1752 = wl  in
        {
          attempting = (uu___255_1752.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___255_1752.ctr);
          defer_ok = (uu___255_1752.defer_ok);
          smt_ok = (uu___255_1752.smt_ok);
          umax_heuristic_ok = (uu___255_1752.umax_heuristic_ok);
          tcenv = (uu___255_1752.tcenv);
          wl_implicits = (uu___255_1752.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___260_1780 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___260_1780.wl_deferred);
         ctr = (uu___260_1780.ctr);
         defer_ok = (uu___260_1780.defer_ok);
         smt_ok = (uu___260_1780.smt_ok);
         umax_heuristic_ok = (uu___260_1780.umax_heuristic_ok);
         tcenv = (uu___260_1780.tcenv);
         wl_implicits = (uu___260_1780.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____1794 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____1794 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____1828 = FStar_Syntax_Util.type_u ()  in
            match uu____1828 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____1840 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____1840 with
                 | (uu____1858,tt,wl1) ->
                     let uu____1861 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                     (uu____1861, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_1867  ->
    match uu___14_1867 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _1873  -> FStar_TypeChecker_Common.TProb _1873) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _1879  -> FStar_TypeChecker_Common.CProb _1879) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1887 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1887 = Prims.int_one
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero  in
  fun uu____1907  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____1949 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____1949 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____1949 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____1949 FStar_TypeChecker_Common.problem *
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
                        let uu____2036 =
                          let uu____2045 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2045]  in
                        FStar_List.append scope uu____2036
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____2088 =
                      let uu____2091 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____2091  in
                    FStar_List.append uu____2088
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____2110 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2110 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2136 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2136;
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
                  (let uu____2210 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2210 with
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
                  (let uu____2298 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2298 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____2336 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2336 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2336 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2336 FStar_TypeChecker_Common.problem *
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
                          let uu____2404 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2404]  in
                        let uu____2423 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____2423
                     in
                  let uu____2426 =
                    let uu____2433 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___343_2444 = wl  in
                       {
                         attempting = (uu___343_2444.attempting);
                         wl_deferred = (uu___343_2444.wl_deferred);
                         ctr = (uu___343_2444.ctr);
                         defer_ok = (uu___343_2444.defer_ok);
                         smt_ok = (uu___343_2444.smt_ok);
                         umax_heuristic_ok =
                           (uu___343_2444.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___343_2444.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2433
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2426 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____2462 =
                              let uu____2467 =
                                let uu____2468 =
                                  let uu____2477 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____2477
                                   in
                                [uu____2468]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2467  in
                            uu____2462 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____2505 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2505;
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
                let uu____2553 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2553;
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
  'Auu____2568 .
    worklist ->
      'Auu____2568 FStar_TypeChecker_Common.problem ->
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
              let uu____2601 =
                let uu____2604 =
                  let uu____2605 =
                    let uu____2612 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____2612)  in
                  FStar_Syntax_Syntax.NT uu____2605  in
                [uu____2604]  in
              FStar_Syntax_Subst.subst uu____2601 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____2636 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2636
        then
          let uu____2644 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2647 = prob_to_string env d  in
          let uu____2649 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2644 uu____2647 uu____2649 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2665 -> failwith "impossible"  in
           let uu____2668 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2684 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2686 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2684, uu____2686)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2693 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2695 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2693, uu____2695)
              in
           match uu____2668 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_2723  ->
            match uu___15_2723 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2735 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2739 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____2739 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_2770  ->
           match uu___16_2770 with
           | UNIV uu____2773 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2780 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2780
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
        (fun uu___17_2808  ->
           match uu___17_2808 with
           | UNIV (u',t) ->
               let uu____2813 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2813
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2820 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2832 =
        let uu____2833 =
          let uu____2834 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____2834
           in
        FStar_Syntax_Subst.compress uu____2833  in
      FStar_All.pipe_right uu____2832 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2846 =
        let uu____2847 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____2847  in
      FStar_All.pipe_right uu____2846 FStar_Syntax_Util.unlazy_emb
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2855 = FStar_Syntax_Util.head_and_args t  in
    match uu____2855 with
    | (h,uu____2874) ->
        let uu____2899 =
          let uu____2900 = FStar_Syntax_Subst.compress h  in
          uu____2900.FStar_Syntax_Syntax.n  in
        (match uu____2899 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____2905 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2918 = should_strongly_reduce t  in
      if uu____2918
      then
        let uu____2921 =
          let uu____2922 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Reify;
              FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant] env t
             in
          FStar_Syntax_Subst.compress uu____2922  in
        FStar_All.pipe_right uu____2921 FStar_Syntax_Util.unlazy_emb
      else whnf' env t
  
let norm_arg :
  'Auu____2932 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____2932) ->
        (FStar_Syntax_Syntax.term * 'Auu____2932)
  =
  fun env  ->
    fun t  ->
      let uu____2955 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2955, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____3007  ->
              match uu____3007 with
              | (x,imp) ->
                  let uu____3026 =
                    let uu___440_3027 = x  in
                    let uu____3028 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___440_3027.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___440_3027.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3028
                    }  in
                  (uu____3026, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3052 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3052
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3056 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3056
        | uu____3059 -> u2  in
      let uu____3060 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3060
  
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
          FStar_TypeChecker_Normalize.normalize_refinement steps env1 t  in
        let rec aux norm1 t11 =
          let t12 = FStar_Syntax_Util.unmeta t11  in
          match t12.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              if norm1
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu____3181 = norm_refinement env t12  in
                 match uu____3181 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3196;
                     FStar_Syntax_Syntax.vars = uu____3197;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3221 =
                       let uu____3223 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3225 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3223 uu____3225
                        in
                     failwith uu____3221)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3241 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3241
          | FStar_Syntax_Syntax.Tm_uinst uu____3242 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3279 =
                   let uu____3280 = FStar_Syntax_Subst.compress t1'  in
                   uu____3280.FStar_Syntax_Syntax.n  in
                 match uu____3279 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3295 -> aux true t1'
                 | uu____3303 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3318 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3349 =
                   let uu____3350 = FStar_Syntax_Subst.compress t1'  in
                   uu____3350.FStar_Syntax_Syntax.n  in
                 match uu____3349 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3365 -> aux true t1'
                 | uu____3373 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3388 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3435 =
                   let uu____3436 = FStar_Syntax_Subst.compress t1'  in
                   uu____3436.FStar_Syntax_Syntax.n  in
                 match uu____3435 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3451 -> aux true t1'
                 | uu____3459 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3474 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3489 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3504 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3519 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3534 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3563 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3596 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3617 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3644 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3672 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3709 ->
              let uu____3716 =
                let uu____3718 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3720 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3718 uu____3720
                 in
              failwith uu____3716
          | FStar_Syntax_Syntax.Tm_ascribed uu____3735 ->
              let uu____3762 =
                let uu____3764 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3766 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3764 uu____3766
                 in
              failwith uu____3762
          | FStar_Syntax_Syntax.Tm_delayed uu____3781 ->
              let uu____3804 =
                let uu____3806 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3808 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3806 uu____3808
                 in
              failwith uu____3804
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3823 =
                let uu____3825 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3827 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3825 uu____3827
                 in
              failwith uu____3823
           in
        let uu____3842 = whnf env t1  in aux false uu____3842
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option))
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        FStar_TypeChecker_Normalize.normalize_refinement steps env t0
  
let (unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun t  ->
      let uu____3903 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3903 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____3944 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3944, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____3971 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____3971 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4031  ->
    match uu____4031 with
    | (t_base,refopt) ->
        let uu____4062 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4062 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4104 =
      let uu____4108 =
        let uu____4111 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4138  ->
                  match uu____4138 with | (uu____4147,uu____4148,x) -> x))
           in
        FStar_List.append wl.attempting uu____4111  in
      FStar_List.map (wl_prob_to_string wl) uu____4108  in
    FStar_All.pipe_right uu____4104 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____4171 .
    ('Auu____4171 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____4183  ->
    match uu____4183 with
    | (uu____4190,c,args) ->
        let uu____4193 = print_ctx_uvar c  in
        let uu____4195 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4193 uu____4195
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4205 = FStar_Syntax_Util.head_and_args t  in
    match uu____4205 with
    | (head1,_args) ->
        let uu____4249 =
          let uu____4250 = FStar_Syntax_Subst.compress head1  in
          uu____4250.FStar_Syntax_Syntax.n  in
        (match uu____4249 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4254 -> true
         | uu____4268 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4276 = FStar_Syntax_Util.head_and_args t  in
    match uu____4276 with
    | (head1,_args) ->
        let uu____4319 =
          let uu____4320 = FStar_Syntax_Subst.compress head1  in
          uu____4320.FStar_Syntax_Syntax.n  in
        (match uu____4319 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4324) -> u
         | uu____4341 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____4366 = FStar_Syntax_Util.head_and_args t  in
      match uu____4366 with
      | (head1,args) ->
          let uu____4413 =
            let uu____4414 = FStar_Syntax_Subst.compress head1  in
            uu____4414.FStar_Syntax_Syntax.n  in
          (match uu____4413 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4422)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4455 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___18_4480  ->
                         match uu___18_4480 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4485 =
                               let uu____4486 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4486.FStar_Syntax_Syntax.n  in
                             (match uu____4485 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4491 -> false)
                         | uu____4493 -> true))
                  in
               (match uu____4455 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4518 =
                        FStar_List.collect
                          (fun uu___19_4530  ->
                             match uu___19_4530 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4534 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4534]
                             | uu____4535 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4518 FStar_List.rev  in
                    let uu____4558 =
                      let uu____4565 =
                        let uu____4574 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___20_4596  ->
                                  match uu___20_4596 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4600 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4600]
                                  | uu____4601 -> []))
                           in
                        FStar_All.pipe_right uu____4574 FStar_List.rev  in
                      let uu____4624 =
                        let uu____4627 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4627  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4565 uu____4624
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____4558 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4663  ->
                                match uu____4663 with
                                | (x,i) ->
                                    let uu____4682 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4682, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4713  ->
                                match uu____4713 with
                                | (a,i) ->
                                    let uu____4732 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4732, i)) args_sol
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
           | uu____4754 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4776 =
          let uu____4799 =
            let uu____4800 = FStar_Syntax_Subst.compress k  in
            uu____4800.FStar_Syntax_Syntax.n  in
          match uu____4799 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4882 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____4882)
              else
                (let uu____4917 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4917 with
                 | (ys',t1,uu____4950) ->
                     let uu____4955 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____4955))
          | uu____4994 ->
              let uu____4995 =
                let uu____5000 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5000)  in
              ((ys, t), uu____4995)
           in
        match uu____4776 with
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
                 let uu____5095 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5095 c  in
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
               (let uu____5173 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5173
                then
                  let uu____5178 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5180 = print_ctx_uvar uv  in
                  let uu____5182 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5178 uu____5180 uu____5182
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5191 =
                   let uu____5193 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____5193  in
                 let uu____5196 =
                   let uu____5199 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5199
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5191 uu____5196 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____5232 =
               let uu____5233 =
                 let uu____5235 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5237 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5235 uu____5237
                  in
               failwith uu____5233  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5303  ->
                       match uu____5303 with
                       | (a,i) ->
                           let uu____5324 =
                             let uu____5325 = FStar_Syntax_Subst.compress a
                                in
                             uu____5325.FStar_Syntax_Syntax.n  in
                           (match uu____5324 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5351 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____5361 =
                 let uu____5363 = is_flex g  in Prims.op_Negation uu____5363
                  in
               if uu____5361
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____5372 = destruct_flex_t g wl  in
                  match uu____5372 with
                  | ((uu____5377,uv1,args),wl1) ->
                      ((let uu____5382 = args_as_binders args  in
                        assign_solution uu____5382 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___692_5384 = wl1  in
              {
                attempting = (uu___692_5384.attempting);
                wl_deferred = (uu___692_5384.wl_deferred);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___692_5384.defer_ok);
                smt_ok = (uu___692_5384.smt_ok);
                umax_heuristic_ok = (uu___692_5384.umax_heuristic_ok);
                tcenv = (uu___692_5384.tcenv);
                wl_implicits = (uu___692_5384.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5409 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5409
         then
           let uu____5414 = FStar_Util.string_of_int pid  in
           let uu____5416 =
             let uu____5418 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____5418 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5414 uu____5416
         else ());
        commit sol;
        (let uu___700_5432 = wl  in
         {
           attempting = (uu___700_5432.attempting);
           wl_deferred = (uu___700_5432.wl_deferred);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___700_5432.defer_ok);
           smt_ok = (uu___700_5432.smt_ok);
           umax_heuristic_ok = (uu___700_5432.umax_heuristic_ok);
           tcenv = (uu___700_5432.tcenv);
           wl_implicits = (uu___700_5432.wl_implicits)
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
             | (uu____5498,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____5526 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____5526
              in
           (let uu____5532 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____5532
            then
              let uu____5537 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____5541 =
                let uu____5543 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____5543 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____5537 uu____5541
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
        let uu____5578 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5578 FStar_Util.set_elements  in
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
      let uu____5618 = occurs uk t  in
      match uu____5618 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5657 =
                 let uu____5659 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5661 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5659 uu____5661
                  in
               FStar_Pervasives_Native.Some uu____5657)
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
            let uu____5781 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5781 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5832 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5889  ->
             match uu____5889 with
             | (x,uu____5901) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____5919 = FStar_List.last bs  in
      match uu____5919 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____5943) ->
          let uu____5954 =
            FStar_Util.prefix_until
              (fun uu___21_5969  ->
                 match uu___21_5969 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____5972 -> false) g
             in
          (match uu____5954 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____5986,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6023 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6023 with
        | (pfx,uu____6033) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6045 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6045 with
             | (uu____6053,src',wl1) ->
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
                 | uu____6167 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6168 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6232  ->
                  fun uu____6233  ->
                    match (uu____6232, uu____6233) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6336 =
                          let uu____6338 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6338
                           in
                        if uu____6336
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6372 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6372
                           then
                             let uu____6389 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6389)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6168 with | (isect,uu____6439) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____6475 'Auu____6476 .
    (FStar_Syntax_Syntax.bv * 'Auu____6475) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____6476) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6534  ->
              fun uu____6535  ->
                match (uu____6534, uu____6535) with
                | ((a,uu____6554),(b,uu____6556)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____6572 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____6572) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6603  ->
           match uu____6603 with
           | (y,uu____6610) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6620 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____6620) Prims.list ->
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
                   let uu____6782 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6782
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6815 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6867 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____6911 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____6932 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___22_6940  ->
    match uu___22_6940 with
    | MisMatch (d1,d2) ->
        let uu____6952 =
          let uu____6954 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____6956 =
            let uu____6958 =
              let uu____6960 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____6960 ")"  in
            Prims.op_Hat ") (" uu____6958  in
          Prims.op_Hat uu____6954 uu____6956  in
        Prims.op_Hat "MisMatch (" uu____6952
    | HeadMatch u ->
        let uu____6967 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____6967
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___23_6976  ->
    match uu___23_6976 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____6993 -> HeadMatch false
  
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
          let uu____7015 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7015 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7026 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7050 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7060 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7087 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7087
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7088 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7089 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7090 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7103 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7117 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7141) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7147,uu____7148) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7190) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7215;
             FStar_Syntax_Syntax.index = uu____7216;
             FStar_Syntax_Syntax.sort = t2;_},uu____7218)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7226 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7227 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7228 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7243 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7250 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7270 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7270
  
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
           { FStar_Syntax_Syntax.blob = uu____7289;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7290;
             FStar_Syntax_Syntax.ltyp = uu____7291;
             FStar_Syntax_Syntax.rng = uu____7292;_},uu____7293)
            ->
            let uu____7304 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7304 t21
        | (uu____7305,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7306;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7307;
             FStar_Syntax_Syntax.ltyp = uu____7308;
             FStar_Syntax_Syntax.rng = uu____7309;_})
            ->
            let uu____7320 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7320
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7332 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7332
            then FullMatch
            else
              (let uu____7337 =
                 let uu____7346 =
                   let uu____7349 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7349  in
                 let uu____7350 =
                   let uu____7353 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7353  in
                 (uu____7346, uu____7350)  in
               MisMatch uu____7337)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7359),FStar_Syntax_Syntax.Tm_uinst (g,uu____7361)) ->
            let uu____7370 = head_matches env f g  in
            FStar_All.pipe_right uu____7370 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7371) -> HeadMatch true
        | (uu____7373,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7377 = FStar_Const.eq_const c d  in
            if uu____7377
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7387),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7389)) ->
            let uu____7422 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7422
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7432),FStar_Syntax_Syntax.Tm_refine (y,uu____7434)) ->
            let uu____7443 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7443 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____7445),uu____7446) ->
            let uu____7451 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____7451 head_match
        | (uu____7452,FStar_Syntax_Syntax.Tm_refine (x,uu____7454)) ->
            let uu____7459 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7459 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7460,FStar_Syntax_Syntax.Tm_type
           uu____7461) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____7463,FStar_Syntax_Syntax.Tm_arrow uu____7464) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____7495),FStar_Syntax_Syntax.Tm_app (head',uu____7497))
            ->
            let uu____7546 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____7546 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____7548),uu____7549) ->
            let uu____7574 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____7574 head_match
        | (uu____7575,FStar_Syntax_Syntax.Tm_app (head1,uu____7577)) ->
            let uu____7602 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____7602 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7603,FStar_Syntax_Syntax.Tm_let
           uu____7604) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____7632,FStar_Syntax_Syntax.Tm_match uu____7633) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7679,FStar_Syntax_Syntax.Tm_abs
           uu____7680) -> HeadMatch true
        | uu____7718 ->
            let uu____7723 =
              let uu____7732 = delta_depth_of_term env t11  in
              let uu____7735 = delta_depth_of_term env t21  in
              (uu____7732, uu____7735)  in
            MisMatch uu____7723
  
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
              let uu____7804 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____7804  in
            (let uu____7806 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7806
             then
               let uu____7811 = FStar_Syntax_Print.term_to_string t  in
               let uu____7813 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7811 uu____7813
             else ());
            (let uu____7818 =
               let uu____7819 = FStar_Syntax_Util.un_uinst head1  in
               uu____7819.FStar_Syntax_Syntax.n  in
             match uu____7818 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7825 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7825 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7839 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7839
                        then
                          let uu____7844 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7844
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7849 ->
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
                        FStar_TypeChecker_Normalize.normalize steps env t  in
                      let uu____7866 =
                        let uu____7868 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____7868 = FStar_Syntax_Util.Equal  in
                      if uu____7866
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____7875 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____7875
                          then
                            let uu____7880 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____7882 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____7880
                              uu____7882
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____7887 -> FStar_Pervasives_Native.None)
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
            (let uu____8039 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8039
             then
               let uu____8044 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8046 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8048 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8044
                 uu____8046 uu____8048
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8076 =
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
               match uu____8076 with
               | (t12,t22) -> aux retry (n_delta + Prims.int_one) t12 t22  in
             let reduce_both_and_try_again d r1 =
               let uu____8124 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8124 with
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
                  uu____8162),uu____8163)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8184 =
                      let uu____8193 = maybe_inline t11  in
                      let uu____8196 = maybe_inline t21  in
                      (uu____8193, uu____8196)  in
                    match uu____8184 with
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
                 (uu____8239,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8240))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8261 =
                      let uu____8270 = maybe_inline t11  in
                      let uu____8273 = maybe_inline t21  in
                      (uu____8270, uu____8273)  in
                    match uu____8261 with
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
             | MisMatch uu____8328 -> fail1 n_delta r t11 t21
             | uu____8337 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8352 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8352
           then
             let uu____8357 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8359 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8361 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8369 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8386 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8386
                    (fun uu____8421  ->
                       match uu____8421 with
                       | (t11,t21) ->
                           let uu____8429 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8431 =
                             let uu____8433 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____8433  in
                           Prims.op_Hat uu____8429 uu____8431))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8357 uu____8359 uu____8361 uu____8369
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____8450 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____8450 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___24_8465  ->
    match uu___24_8465 with
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
      let uu___1204_8514 = p  in
      let uu____8517 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8518 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1204_8514.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8517;
        FStar_TypeChecker_Common.relation =
          (uu___1204_8514.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8518;
        FStar_TypeChecker_Common.element =
          (uu___1204_8514.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1204_8514.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1204_8514.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1204_8514.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1204_8514.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1204_8514.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8533 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____8533
            (fun _8538  -> FStar_TypeChecker_Common.TProb _8538)
      | FStar_TypeChecker_Common.CProb uu____8539 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____8562 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____8562 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8570 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8570 with
           | (lh,lhs_args) ->
               let uu____8617 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8617 with
                | (rh,rhs_args) ->
                    let uu____8664 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8677,FStar_Syntax_Syntax.Tm_uvar uu____8678)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8767 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8794,uu____8795)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8810,FStar_Syntax_Syntax.Tm_uvar uu____8811)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8826,FStar_Syntax_Syntax.Tm_arrow uu____8827)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1255_8857 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1255_8857.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1255_8857.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1255_8857.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1255_8857.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1255_8857.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1255_8857.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1255_8857.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1255_8857.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1255_8857.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8860,FStar_Syntax_Syntax.Tm_type uu____8861)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1255_8877 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1255_8877.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1255_8877.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1255_8877.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1255_8877.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1255_8877.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1255_8877.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1255_8877.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1255_8877.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1255_8877.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____8880,FStar_Syntax_Syntax.Tm_uvar uu____8881)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1255_8897 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1255_8897.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1255_8897.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1255_8897.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1255_8897.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1255_8897.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1255_8897.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1255_8897.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1255_8897.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1255_8897.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____8900,FStar_Syntax_Syntax.Tm_uvar uu____8901)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8916,uu____8917)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8932,FStar_Syntax_Syntax.Tm_uvar uu____8933)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8948,uu____8949) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____8664 with
                     | (rank,tp1) ->
                         let uu____8962 =
                           FStar_All.pipe_right
                             (let uu___1275_8966 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1275_8966.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1275_8966.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1275_8966.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1275_8966.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1275_8966.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1275_8966.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1275_8966.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1275_8966.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1275_8966.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _8969  ->
                                FStar_TypeChecker_Common.TProb _8969)
                            in
                         (rank, uu____8962))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8973 =
            FStar_All.pipe_right
              (let uu___1279_8977 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1279_8977.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1279_8977.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1279_8977.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1279_8977.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1279_8977.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1279_8977.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1279_8977.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1279_8977.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1279_8977.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _8980  -> FStar_TypeChecker_Common.CProb _8980)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____8973)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9040 probs =
      match uu____9040 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9121 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____9142 = rank wl.tcenv hd1  in
               (match uu____9142 with
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
                      (let uu____9203 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9208 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9208)
                          in
                       if uu____9203
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
          let uu____9281 = FStar_Syntax_Util.head_and_args t  in
          match uu____9281 with
          | (hd1,uu____9300) ->
              let uu____9325 =
                let uu____9326 = FStar_Syntax_Subst.compress hd1  in
                uu____9326.FStar_Syntax_Syntax.n  in
              (match uu____9325 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9331) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9366  ->
                           match uu____9366 with
                           | (y,uu____9375) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9398  ->
                                       match uu____9398 with
                                       | (x,uu____9407) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9412 -> false)
           in
        let uu____9414 = rank tcenv p  in
        match uu____9414 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9423 -> true
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
  | UFailed of Prims.string 
let (uu___is_UDeferred : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____9460 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9479 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9499 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> Prims.string) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
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
                        let uu____9561 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9561 with
                        | (k,uu____9569) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9582 -> false)))
            | uu____9584 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9636 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9644 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9644 = Prims.int_zero))
                           in
                        if uu____9636 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9665 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9673 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9673 = Prims.int_zero))
                      in
                   Prims.op_Negation uu____9665)
               in
            let uu____9677 = filter1 u12  in
            let uu____9680 = filter1 u22  in (uu____9677, uu____9680)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then UFailed "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9715 = filter_out_common_univs us1 us2  in
                   (match uu____9715 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____9775 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____9775 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9778 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          (let uu____9789 =
                             let uu____9791 =
                               FStar_Syntax_Print.univ_to_string u12  in
                             let uu____9793 =
                               FStar_Syntax_Print.univ_to_string u22  in
                             FStar_Util.format2
                               "Unable to unify universes: %s and %s"
                               uu____9791 uu____9793
                              in
                           UFailed uu____9789))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9819 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____9819 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9845 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____9845 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____9848 ->
                   let uu____9853 =
                     let uu____9855 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____9857 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format3
                       "Unable to unify universes: %s and %s (%s)" uu____9855
                       uu____9857 msg
                      in
                   UFailed uu____9853)
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9860,uu____9861) ->
              let uu____9863 =
                let uu____9865 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9867 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9865 uu____9867
                 in
              failwith uu____9863
          | (FStar_Syntax_Syntax.U_unknown ,uu____9870) ->
              let uu____9871 =
                let uu____9873 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9875 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9873 uu____9875
                 in
              failwith uu____9871
          | (uu____9878,FStar_Syntax_Syntax.U_bvar uu____9879) ->
              let uu____9881 =
                let uu____9883 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9885 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9883 uu____9885
                 in
              failwith uu____9881
          | (uu____9888,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9889 =
                let uu____9891 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9893 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9891 uu____9893
                 in
              failwith uu____9889
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9923 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____9923
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____9940 = occurs_univ v1 u3  in
              if uu____9940
              then
                let uu____9943 =
                  let uu____9945 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9947 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9945 uu____9947
                   in
                try_umax_components u11 u21 uu____9943
              else
                (let uu____9952 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9952)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____9964 = occurs_univ v1 u3  in
              if uu____9964
              then
                let uu____9967 =
                  let uu____9969 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9971 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9969 uu____9971
                   in
                try_umax_components u11 u21 uu____9967
              else
                (let uu____9976 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9976)
          | (FStar_Syntax_Syntax.U_max uu____9977,uu____9978) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9986 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9986
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9992,FStar_Syntax_Syntax.U_max uu____9993) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10001 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10001
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10007,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10009,FStar_Syntax_Syntax.U_name uu____10010) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10012) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10014) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10016,FStar_Syntax_Syntax.U_succ uu____10017) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10019,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
  
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
      let uu____10126 = bc1  in
      match uu____10126 with
      | (bs1,mk_cod1) ->
          let uu____10170 = bc2  in
          (match uu____10170 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10281 = aux xs ys  in
                     (match uu____10281 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10364 =
                       let uu____10371 = mk_cod1 xs  in ([], uu____10371)  in
                     let uu____10374 =
                       let uu____10381 = mk_cod2 ys  in ([], uu____10381)  in
                     (uu____10364, uu____10374)
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
                  let uu____10450 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10450 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____10453 =
                    let uu____10454 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____10454 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____10453
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____10459 = has_type_guard t1 t2  in (uu____10459, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____10460 = has_type_guard t2 t1  in (uu____10460, wl)
  
let is_flex_pat :
  'Auu____10470 'Auu____10471 'Auu____10472 .
    ('Auu____10470 * 'Auu____10471 * 'Auu____10472 Prims.list) -> Prims.bool
  =
  fun uu___25_10486  ->
    match uu___25_10486 with
    | (uu____10495,uu____10496,[]) -> true
    | uu____10500 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____10533 = f  in
      match uu____10533 with
      | (uu____10540,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____10541;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10542;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____10545;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____10546;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____10547;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____10548;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10618  ->
                 match uu____10618 with
                 | (y,uu____10627) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____10781 =
                  let uu____10796 =
                    let uu____10799 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____10799  in
                  ((FStar_List.rev pat_binders), uu____10796)  in
                FStar_Pervasives_Native.Some uu____10781
            | (uu____10832,[]) ->
                let uu____10863 =
                  let uu____10878 =
                    let uu____10881 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____10881  in
                  ((FStar_List.rev pat_binders), uu____10878)  in
                FStar_Pervasives_Native.Some uu____10863
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____10972 =
                  let uu____10973 = FStar_Syntax_Subst.compress a  in
                  uu____10973.FStar_Syntax_Syntax.n  in
                (match uu____10972 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____10993 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____10993
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1603_11023 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1603_11023.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1603_11023.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____11027 =
                            let uu____11028 =
                              let uu____11035 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11035)  in
                            FStar_Syntax_Syntax.NT uu____11028  in
                          [uu____11027]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___1609_11051 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1609_11051.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1609_11051.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11052 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11092 =
                  let uu____11107 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11107  in
                (match uu____11092 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11182 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11215 ->
               let uu____11216 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11216 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____11538 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____11538
       then
         let uu____11543 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11543
       else ());
      (let uu____11548 = next_prob probs  in
       match uu____11548 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___1634_11575 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___1634_11575.wl_deferred);
               ctr = (uu___1634_11575.ctr);
               defer_ok = (uu___1634_11575.defer_ok);
               smt_ok = (uu___1634_11575.smt_ok);
               umax_heuristic_ok = (uu___1634_11575.umax_heuristic_ok);
               tcenv = (uu___1634_11575.tcenv);
               wl_implicits = (uu___1634_11575.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11584 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____11584
                 then
                   let uu____11587 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____11587
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
                       solve env
                         (defer "deferring flex_rigid or flex_flex subtyping"
                            hd1 probs1)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1646_11599 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1646_11599.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1646_11599.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1646_11599.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1646_11599.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1646_11599.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1646_11599.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1646_11599.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1646_11599.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1646_11599.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____11625 ->
                let uu____11636 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11707  ->
                          match uu____11707 with
                          | (c,uu____11718,uu____11719) -> c < probs.ctr))
                   in
                (match uu____11636 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11774 =
                            let uu____11779 =
                              FStar_List.map
                                (fun uu____11797  ->
                                   match uu____11797 with
                                   | (uu____11811,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____11779, (probs.wl_implicits))  in
                          Success uu____11774
                      | uu____11819 ->
                          let uu____11830 =
                            let uu___1664_11831 = probs  in
                            let uu____11832 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____11855  ->
                                      match uu____11855 with
                                      | (uu____11864,uu____11865,y) -> y))
                               in
                            {
                              attempting = uu____11832;
                              wl_deferred = rest;
                              ctr = (uu___1664_11831.ctr);
                              defer_ok = (uu___1664_11831.defer_ok);
                              smt_ok = (uu___1664_11831.smt_ok);
                              umax_heuristic_ok =
                                (uu___1664_11831.umax_heuristic_ok);
                              tcenv = (uu___1664_11831.tcenv);
                              wl_implicits = (uu___1664_11831.wl_implicits)
                            }  in
                          solve env uu____11830))))

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
            let uu____11876 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____11876 with
            | USolved wl1 ->
                let uu____11878 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____11878
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 -> solve env (defer "" orig wl1)

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
                  let uu____11932 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____11932 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____11935 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____11948;
                  FStar_Syntax_Syntax.vars = uu____11949;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____11952;
                  FStar_Syntax_Syntax.vars = uu____11953;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____11966,uu____11967) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____11975,FStar_Syntax_Syntax.Tm_uinst uu____11976) ->
                failwith "Impossible: expect head symbols to match"
            | uu____11984 -> USolved wl

and (giveup_or_defer :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> Prims.string -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun msg  ->
          if wl.defer_ok
          then
            ((let uu____11996 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____11996
              then
                let uu____12001 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12001 msg
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
               let uu____12093 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12093 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12148 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12148
                then
                  let uu____12153 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12155 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12153 uu____12155
                else ());
               (let uu____12160 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12160 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12206 = eq_prob t1 t2 wl2  in
                         (match uu____12206 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12227 ->
                         let uu____12236 = eq_prob t1 t2 wl2  in
                         (match uu____12236 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____12286 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____12301 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____12302 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____12301, uu____12302)
                           | FStar_Pervasives_Native.None  ->
                               let uu____12307 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____12308 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____12307, uu____12308)
                            in
                         (match uu____12286 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12339 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____12339 with
                                | (t1_hd,t1_args) ->
                                    let uu____12384 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____12384 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12450 =
                                              let uu____12457 =
                                                let uu____12468 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____12468 :: t1_args  in
                                              let uu____12485 =
                                                let uu____12494 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____12494 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____12543  ->
                                                   fun uu____12544  ->
                                                     fun uu____12545  ->
                                                       match (uu____12543,
                                                               uu____12544,
                                                               uu____12545)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____12595),
                                                          (a2,uu____12597))
                                                           ->
                                                           let uu____12634 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____12634
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12457
                                                uu____12485
                                               in
                                            match uu____12450 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1818_12660 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___1818_12660.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1818_12660.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1818_12660.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12672 =
                                                  solve env1 wl'  in
                                                (match uu____12672 with
                                                 | Success (uu____12675,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___1827_12679
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___1827_12679.attempting);
                                                            wl_deferred =
                                                              (uu___1827_12679.wl_deferred);
                                                            ctr =
                                                              (uu___1827_12679.ctr);
                                                            defer_ok =
                                                              (uu___1827_12679.defer_ok);
                                                            smt_ok =
                                                              (uu___1827_12679.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___1827_12679.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___1827_12679.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____12680 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____12713 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____12713 with
                                | (t1_base,p1_opt) ->
                                    let uu____12749 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____12749 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____12848 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____12848
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
                                               let uu____12901 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____12901
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
                                               let uu____12933 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____12933
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
                                               let uu____12965 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____12965
                                           | uu____12968 -> t_base  in
                                         let uu____12985 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____12985 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____12999 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____12999, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13006 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13006 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13042 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13042 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13078 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13078
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
                              let uu____13102 = combine t11 t21 wl2  in
                              (match uu____13102 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13135 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13135
                                     then
                                       let uu____13140 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13140
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13182 ts1 =
               match uu____13182 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13245 = pairwise out t wl2  in
                        (match uu____13245 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____13281 =
               let uu____13292 = FStar_List.hd ts  in (uu____13292, [], wl1)
                in
             let uu____13301 = FStar_List.tl ts  in
             aux uu____13281 uu____13301  in
           let uu____13308 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____13308 with
           | (this_flex,this_rigid) ->
               let uu____13334 =
                 let uu____13335 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____13335.FStar_Syntax_Syntax.n  in
               (match uu____13334 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____13360 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____13360
                    then
                      let uu____13363 = destruct_flex_t this_flex wl  in
                      (match uu____13363 with
                       | (flex,wl1) ->
                           let uu____13370 = quasi_pattern env flex  in
                           (match uu____13370 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____13389 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____13389
                                  then
                                    let uu____13394 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13394
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13401 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___1929_13404 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___1929_13404.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___1929_13404.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___1929_13404.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___1929_13404.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___1929_13404.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___1929_13404.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___1929_13404.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___1929_13404.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___1929_13404.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____13401)
                | uu____13405 ->
                    ((let uu____13407 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13407
                      then
                        let uu____13412 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13412
                      else ());
                     (let uu____13417 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____13417 with
                      | (u,_args) ->
                          let uu____13460 =
                            let uu____13461 = FStar_Syntax_Subst.compress u
                               in
                            uu____13461.FStar_Syntax_Syntax.n  in
                          (match uu____13460 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____13489 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____13489 with
                                 | (u',uu____13508) ->
                                     let uu____13533 =
                                       let uu____13534 = whnf env u'  in
                                       uu____13534.FStar_Syntax_Syntax.n  in
                                     (match uu____13533 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13556 -> false)
                                  in
                               let uu____13558 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___26_13581  ->
                                         match uu___26_13581 with
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
                                              | uu____13595 -> false)
                                         | uu____13599 -> false))
                                  in
                               (match uu____13558 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____13614 = whnf env this_rigid
                                         in
                                      let uu____13615 =
                                        FStar_List.collect
                                          (fun uu___27_13621  ->
                                             match uu___27_13621 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13627 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____13627]
                                             | uu____13631 -> [])
                                          bounds_probs
                                         in
                                      uu____13614 :: uu____13615  in
                                    let uu____13632 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____13632 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____13665 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____13680 =
                                               let uu____13681 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____13681.FStar_Syntax_Syntax.n
                                                in
                                             match uu____13680 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13693 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13693)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13704 -> bound  in
                                           let uu____13705 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____13705)  in
                                         (match uu____13665 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13740 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____13740
                                                then
                                                  let wl'1 =
                                                    let uu___1989_13746 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___1989_13746.wl_deferred);
                                                      ctr =
                                                        (uu___1989_13746.ctr);
                                                      defer_ok =
                                                        (uu___1989_13746.defer_ok);
                                                      smt_ok =
                                                        (uu___1989_13746.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___1989_13746.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___1989_13746.tcenv);
                                                      wl_implicits =
                                                        (uu___1989_13746.wl_implicits)
                                                    }  in
                                                  let uu____13747 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13747
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13753 =
                                                  solve_t env eq_prob
                                                    (let uu___1994_13755 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___1994_13755.wl_deferred);
                                                       ctr =
                                                         (uu___1994_13755.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___1994_13755.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___1994_13755.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___1994_13755.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____13753 with
                                                | Success (uu____13757,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2000_13760 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2000_13760.wl_deferred);
                                                        ctr =
                                                          (uu___2000_13760.ctr);
                                                        defer_ok =
                                                          (uu___2000_13760.defer_ok);
                                                        smt_ok =
                                                          (uu___2000_13760.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2000_13760.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2000_13760.tcenv);
                                                        wl_implicits =
                                                          (uu___2000_13760.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2003_13762 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2003_13762.attempting);
                                                        wl_deferred =
                                                          (uu___2003_13762.wl_deferred);
                                                        ctr =
                                                          (uu___2003_13762.ctr);
                                                        defer_ok =
                                                          (uu___2003_13762.defer_ok);
                                                        smt_ok =
                                                          (uu___2003_13762.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2003_13762.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2003_13762.tcenv);
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
                                                    let uu____13778 =
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
                                                    ((let uu____13792 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____13792
                                                      then
                                                        let uu____13797 =
                                                          let uu____13799 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____13799
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13797
                                                      else ());
                                                     (let uu____13812 =
                                                        let uu____13827 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____13827)
                                                         in
                                                      match uu____13812 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____13849))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13875 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____13875
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
                                                                  let uu____13895
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____13895))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13920 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____13920
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
                                                                    let uu____13940
                                                                    =
                                                                    let uu____13945
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____13945
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____13940
                                                                    [] wl2
                                                                     in
                                                                  let uu____13951
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____13951))))
                                                      | uu____13952 ->
                                                          giveup env
                                                            (Prims.op_Hat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____13968 when flip ->
                               let uu____13969 =
                                 let uu____13971 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____13973 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____13971 uu____13973
                                  in
                               failwith uu____13969
                           | uu____13976 ->
                               let uu____13977 =
                                 let uu____13979 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____13981 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____13979 uu____13981
                                  in
                               failwith uu____13977)))))

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
                      (fun uu____14017  ->
                         match uu____14017 with
                         | (x,i) ->
                             let uu____14036 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14036, i)) bs_lhs
                     in
                  let uu____14039 = lhs  in
                  match uu____14039 with
                  | (uu____14040,u_lhs,uu____14042) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14139 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14149 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14149, univ)
                             in
                          match uu____14139 with
                          | (k,univ) ->
                              let uu____14156 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14156 with
                               | (uu____14173,u,wl3) ->
                                   let uu____14176 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14176, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14202 =
                              let uu____14215 =
                                let uu____14226 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14226 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____14277  ->
                                   fun uu____14278  ->
                                     match (uu____14277, uu____14278) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____14379 =
                                           let uu____14386 =
                                             let uu____14389 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____14389
                                              in
                                           copy_uvar u_lhs [] uu____14386 wl2
                                            in
                                         (match uu____14379 with
                                          | (uu____14418,t_a,wl3) ->
                                              let uu____14421 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____14421 with
                                               | (uu____14440,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14215
                                ([], wl1)
                               in
                            (match uu____14202 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2113_14496 = ct  in
                                   let uu____14497 =
                                     let uu____14500 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14500
                                      in
                                   let uu____14515 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2113_14496.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2113_14496.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14497;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14515;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2113_14496.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2116_14533 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2116_14533.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2116_14533.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14536 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____14536 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14598 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14598 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____14609 =
                                          let uu____14614 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____14614)  in
                                        TERM uu____14609  in
                                      let uu____14615 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____14615 with
                                       | (sub_prob,wl3) ->
                                           let uu____14629 =
                                             let uu____14630 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____14630
                                              in
                                           solve env uu____14629))
                             | (x,imp)::formals2 ->
                                 let uu____14652 =
                                   let uu____14659 =
                                     let uu____14662 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____14662
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14659 wl1
                                    in
                                 (match uu____14652 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____14683 =
                                          let uu____14686 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14686
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14683 u_x
                                         in
                                      let uu____14687 =
                                        let uu____14690 =
                                          let uu____14693 =
                                            let uu____14694 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____14694, imp)  in
                                          [uu____14693]  in
                                        FStar_List.append bs_terms
                                          uu____14690
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14687 formals2 wl2)
                              in
                           let uu____14721 = occurs_check u_lhs arrow1  in
                           (match uu____14721 with
                            | (uu____14734,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14750 =
                                    let uu____14752 = FStar_Option.get msg
                                       in
                                    Prims.op_Hat "occurs-check failed: "
                                      uu____14752
                                     in
                                  giveup_or_defer env orig wl uu____14750
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
              (let uu____14785 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____14785
               then
                 let uu____14790 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____14793 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14790 (rel_to_string (p_rel orig)) uu____14793
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____14924 = rhs wl1 scope env1 subst1  in
                     (match uu____14924 with
                      | (rhs_prob,wl2) ->
                          ((let uu____14947 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____14947
                            then
                              let uu____14952 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____14952
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15030 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15030 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2185_15032 = hd1  in
                       let uu____15033 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2185_15032.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2185_15032.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15033
                       }  in
                     let hd21 =
                       let uu___2188_15037 = hd2  in
                       let uu____15038 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2188_15037.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2188_15037.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15038
                       }  in
                     let uu____15041 =
                       let uu____15046 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15046
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15041 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____15069 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst1
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15069
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15076 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____15076 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15148 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15148
                                  in
                               ((let uu____15166 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15166
                                 then
                                   let uu____15171 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15173 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15171
                                     uu____15173
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____15208 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15244 = aux wl [] env [] bs1 bs2  in
               match uu____15244 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15303 = attempt sub_probs wl2  in
                   solve env1 uu____15303)

and (try_solve_without_smt_or_else :
  FStar_TypeChecker_Env.env ->
    worklist ->
      (FStar_TypeChecker_Env.env -> worklist -> solution) ->
        (FStar_TypeChecker_Env.env ->
           worklist ->
             (FStar_TypeChecker_Common.prob * Prims.string) -> solution)
          -> solution)
  =
  fun env  ->
    fun wl  ->
      fun try_solve  ->
        fun else_solve  ->
          let wl' =
            let uu___2226_15324 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2226_15324.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2226_15324.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15337 = try_solve env wl'  in
          match uu____15337 with
          | Success (uu____15338,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2235_15342 = wl  in
                  {
                    attempting = (uu___2235_15342.attempting);
                    wl_deferred = (uu___2235_15342.wl_deferred);
                    ctr = (uu___2235_15342.ctr);
                    defer_ok = (uu___2235_15342.defer_ok);
                    smt_ok = (uu___2235_15342.smt_ok);
                    umax_heuristic_ok = (uu___2235_15342.umax_heuristic_ok);
                    tcenv = (uu___2235_15342.tcenv);
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
        (let uu____15354 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15354 wl)

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
              let uu____15368 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15368 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15402 = lhs1  in
              match uu____15402 with
              | (uu____15405,ctx_u,uu____15407) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15415 ->
                        let uu____15416 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15416 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15465 = quasi_pattern env1 lhs1  in
              match uu____15465 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15499) ->
                  let uu____15504 = lhs1  in
                  (match uu____15504 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15519 = occurs_check ctx_u rhs1  in
                       (match uu____15519 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15570 =
                                let uu____15578 =
                                  let uu____15580 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15580
                                   in
                                FStar_Util.Inl uu____15578  in
                              (uu____15570, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15608 =
                                 let uu____15610 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15610  in
                               if uu____15608
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15637 =
                                    let uu____15645 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15645  in
                                  let uu____15651 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____15637, uu____15651)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____15695 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____15695 with
              | (rhs_hd,args) ->
                  let uu____15738 = FStar_Util.prefix args  in
                  (match uu____15738 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15810 = lhs1  in
                       (match uu____15810 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____15814 =
                              let uu____15825 =
                                let uu____15832 =
                                  let uu____15835 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____15835
                                   in
                                copy_uvar u_lhs [] uu____15832 wl1  in
                              match uu____15825 with
                              | (uu____15862,t_last_arg,wl2) ->
                                  let uu____15865 =
                                    let uu____15872 =
                                      let uu____15873 =
                                        let uu____15882 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____15882]  in
                                      FStar_List.append bs_lhs uu____15873
                                       in
                                    copy_uvar u_lhs uu____15872 t_res_lhs wl2
                                     in
                                  (match uu____15865 with
                                   | (uu____15917,lhs',wl3) ->
                                       let uu____15920 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____15920 with
                                        | (uu____15937,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____15814 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____15958 =
                                     let uu____15959 =
                                       let uu____15964 =
                                         let uu____15965 =
                                           let uu____15968 =
                                             let uu____15973 =
                                               let uu____15974 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____15974]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____15973
                                              in
                                           uu____15968
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____15965
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____15964)  in
                                     TERM uu____15959  in
                                   [uu____15958]  in
                                 let uu____15999 =
                                   let uu____16006 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____16006 with
                                   | (p1,wl3) ->
                                       let uu____16026 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____16026 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____15999 with
                                  | (sub_probs,wl3) ->
                                      let uu____16058 =
                                        let uu____16059 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____16059  in
                                      solve env1 uu____16058))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16093 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16093 with
                | (uu____16111,args) ->
                    (match args with | [] -> false | uu____16147 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16166 =
                  let uu____16167 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16167.FStar_Syntax_Syntax.n  in
                match uu____16166 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16171 -> true
                | uu____16187 -> false  in
              let uu____16189 = quasi_pattern env1 lhs1  in
              match uu____16189 with
              | FStar_Pervasives_Native.None  ->
                  let uu____16200 =
                    let uu____16202 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                      uu____16202
                     in
                  giveup_or_defer env1 orig1 wl1 uu____16200
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16211 = is_app rhs1  in
                  if uu____16211
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____16216 = is_arrow rhs1  in
                     if uu____16216
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____16221 =
                          let uu____16223 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heuristic cannot solve %s; rhs not an app or arrow"
                            uu____16223
                           in
                        giveup_or_defer env1 orig1 wl1 uu____16221))
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then giveup_or_defer env orig wl "flex-rigid subtyping"
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then giveup_or_defer env orig wl "flex-rigid subtyping"
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____16234 = lhs  in
                (match uu____16234 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16238 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16238 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16256 =
                              let uu____16260 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16260
                               in
                            FStar_All.pipe_right uu____16256
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16281 = occurs_check ctx_uv rhs1  in
                          (match uu____16281 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16310 =
                                   let uu____16312 = FStar_Option.get msg  in
                                   Prims.op_Hat "occurs-check failed: "
                                     uu____16312
                                    in
                                 giveup_or_defer env orig wl uu____16310
                               else
                                 (let uu____16318 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____16318
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____16325 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____16325
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____16329 =
                                         let uu____16331 =
                                           names_to_string1 fvs2  in
                                         let uu____16333 =
                                           names_to_string1 fvs1  in
                                         let uu____16335 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____16331 uu____16333
                                           uu____16335
                                          in
                                       giveup_or_defer env orig wl
                                         uu____16329)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16347 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____16354 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16354 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16380 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16380
                             | (FStar_Util.Inl msg,uu____16382) ->
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
                then giveup_or_defer env orig wl "flex-flex subtyping"
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then giveup_or_defer env orig wl "flex-flex subtyping"
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then giveup_or_defer env orig wl "flex-flex non-pattern"
                else
                  (let uu____16427 =
                     let uu____16444 = quasi_pattern env lhs  in
                     let uu____16451 = quasi_pattern env rhs  in
                     (uu____16444, uu____16451)  in
                   match uu____16427 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16494 = lhs  in
                       (match uu____16494 with
                        | ({ FStar_Syntax_Syntax.n = uu____16495;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____16497;_},u_lhs,uu____16499)
                            ->
                            let uu____16502 = rhs  in
                            (match uu____16502 with
                             | (uu____16503,u_rhs,uu____16505) ->
                                 let uu____16506 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16506
                                 then
                                   let uu____16513 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16513
                                 else
                                   (let uu____16516 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16516 with
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
                                        let uu____16548 =
                                          let uu____16555 =
                                            let uu____16558 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16558
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16555
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____16548 with
                                         | (uu____16570,w,wl1) ->
                                             let w_app =
                                               let uu____16576 =
                                                 let uu____16581 =
                                                   FStar_List.map
                                                     (fun uu____16592  ->
                                                        match uu____16592
                                                        with
                                                        | (z,uu____16600) ->
                                                            let uu____16605 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____16605) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____16581
                                                  in
                                               uu____16576
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16607 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16607
                                               then
                                                 let uu____16612 =
                                                   let uu____16616 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16618 =
                                                     let uu____16622 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____16624 =
                                                       let uu____16628 =
                                                         term_to_string w  in
                                                       let uu____16630 =
                                                         let uu____16634 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____16643 =
                                                           let uu____16647 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____16656 =
                                                             let uu____16660
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____16660]
                                                              in
                                                           uu____16647 ::
                                                             uu____16656
                                                            in
                                                         uu____16634 ::
                                                           uu____16643
                                                          in
                                                       uu____16628 ::
                                                         uu____16630
                                                        in
                                                     uu____16622 ::
                                                       uu____16624
                                                      in
                                                   uu____16616 :: uu____16618
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16612
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____16677 =
                                                     let uu____16682 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____16682)  in
                                                   TERM uu____16677  in
                                                 let uu____16683 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____16683
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____16691 =
                                                        let uu____16696 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____16696)
                                                         in
                                                      TERM uu____16691  in
                                                    [s1; s2])
                                                  in
                                               let uu____16697 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____16697))))))
                   | uu____16698 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____16769 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____16769
            then
              let uu____16774 = FStar_Syntax_Print.term_to_string t1  in
              let uu____16776 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____16778 = FStar_Syntax_Print.term_to_string t2  in
              let uu____16780 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____16774 uu____16776 uu____16778 uu____16780
            else ());
           (let uu____16791 = FStar_Syntax_Util.head_and_args t1  in
            match uu____16791 with
            | (head1,args1) ->
                let uu____16834 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____16834 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____16904 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____16904 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              k false (defer "universe constraints" orig wl3))
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____16930 =
                         let uu____16932 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____16934 = args_to_string args1  in
                         let uu____16938 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____16940 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____16932 uu____16934 uu____16938 uu____16940
                          in
                       giveup env1 uu____16930 orig
                     else
                       (let uu____16947 =
                          (nargs = Prims.int_zero) ||
                            (let uu____16952 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____16952 = FStar_Syntax_Util.Equal)
                           in
                        if uu____16947
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2484_16956 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2484_16956.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2484_16956.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2484_16956.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2484_16956.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2484_16956.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2484_16956.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2484_16956.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2484_16956.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____16966 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____16966
                                    else solve env1 wl2))
                        else
                          (let uu____16971 = base_and_refinement env1 t1  in
                           match uu____16971 with
                           | (base1,refinement1) ->
                               let uu____16996 = base_and_refinement env1 t2
                                  in
                               (match uu____16996 with
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
                                           let uu____17161 =
                                             FStar_List.fold_right
                                               (fun uu____17201  ->
                                                  fun uu____17202  ->
                                                    match (uu____17201,
                                                            uu____17202)
                                                    with
                                                    | (((a1,uu____17254),
                                                        (a2,uu____17256)),
                                                       (probs,wl3)) ->
                                                        let uu____17305 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17305
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17161 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17348 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17348
                                                 then
                                                   let uu____17353 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17353
                                                 else ());
                                                (let uu____17359 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17359
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
                                                    (let uu____17386 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17386 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17402 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17402
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17410 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17410))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____17434 =
                                                    mk_sub_probs wl3  in
                                                  match uu____17434 with
                                                  | (subprobs,wl4) ->
                                                      let wl5 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          [] wl4
                                                         in
                                                      let uu____17448 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____17448)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17474 =
                                           match uu____17474 with
                                           | (prob,reason) ->
                                               ((let uu____17485 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17485
                                                 then
                                                   let uu____17490 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____17492 =
                                                     prob_to_string env2 prob
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____17490 uu____17492
                                                     reason
                                                 else ());
                                                (let uu____17497 =
                                                   let uu____17506 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____17509 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____17506, uu____17509)
                                                    in
                                                 match uu____17497 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____17522 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____17522 with
                                                      | (head1',uu____17540)
                                                          ->
                                                          let uu____17565 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____17565
                                                           with
                                                           | (head2',uu____17583)
                                                               ->
                                                               let uu____17608
                                                                 =
                                                                 let uu____17613
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____17614
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____17613,
                                                                   uu____17614)
                                                                  in
                                                               (match uu____17608
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____17616
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17616
                                                                    then
                                                                    let uu____17621
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____17623
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____17625
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____17627
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17621
                                                                    uu____17623
                                                                    uu____17625
                                                                    uu____17627
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____17632
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2570_17640
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2570_17640.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2570_17640.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2570_17640.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2570_17640.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2570_17640.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2570_17640.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2570_17640.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2570_17640.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____17642
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17642
                                                                    then
                                                                    let uu____17647
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____17647
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____17652 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____17664 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____17664 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____17672 =
                                             let uu____17673 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____17673.FStar_Syntax_Syntax.n
                                              in
                                           match uu____17672 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____17678 -> false  in
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
                                          | uu____17681 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____17684 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2590_17720 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2590_17720.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2590_17720.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2590_17720.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2590_17720.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2590_17720.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2590_17720.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2590_17720.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2590_17720.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____17796 = destruct_flex_t scrutinee wl1  in
             match uu____17796 with
             | ((_t,uv,_args),wl2) ->
                 let uu____17807 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____17807 with
                  | (xs,pat_term,uu____17823,uu____17824) ->
                      let uu____17829 =
                        FStar_List.fold_left
                          (fun uu____17852  ->
                             fun x  ->
                               match uu____17852 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____17873 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____17873 with
                                    | (uu____17892,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____17829 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____17913 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____17913 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2630_17930 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2630_17930.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2630_17930.umax_heuristic_ok);
                                    tcenv = (uu___2630_17930.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____17942 = solve env1 wl'  in
                                (match uu____17942 with
                                 | Success (uu____17945,imps) ->
                                     let wl'1 =
                                       let uu___2638_17948 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2638_17948.wl_deferred);
                                         ctr = (uu___2638_17948.ctr);
                                         defer_ok =
                                           (uu___2638_17948.defer_ok);
                                         smt_ok = (uu___2638_17948.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2638_17948.umax_heuristic_ok);
                                         tcenv = (uu___2638_17948.tcenv);
                                         wl_implicits =
                                           (uu___2638_17948.wl_implicits)
                                       }  in
                                     let uu____17949 = solve env1 wl'1  in
                                     (match uu____17949 with
                                      | Success (uu____17952,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2646_17956 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2646_17956.attempting);
                                                 wl_deferred =
                                                   (uu___2646_17956.wl_deferred);
                                                 ctr = (uu___2646_17956.ctr);
                                                 defer_ok =
                                                   (uu___2646_17956.defer_ok);
                                                 smt_ok =
                                                   (uu___2646_17956.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2646_17956.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2646_17956.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____17957 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____17964 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____17987 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____17987
                 then
                   let uu____17992 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____17994 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____17992 uu____17994
                 else ());
                (let uu____17999 =
                   let uu____18020 =
                     let uu____18029 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18029)  in
                   let uu____18036 =
                     let uu____18045 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18045)  in
                   (uu____18020, uu____18036)  in
                 match uu____17999 with
                 | ((uu____18075,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18078;
                                   FStar_Syntax_Syntax.vars = uu____18079;_}),
                    (s,t)) ->
                     let uu____18150 =
                       let uu____18152 = is_flex scrutinee  in
                       Prims.op_Negation uu____18152  in
                     if uu____18150
                     then
                       ((let uu____18163 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18163
                         then
                           let uu____18168 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18168
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18187 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18187
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18202 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18202
                           then
                             let uu____18207 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18209 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18207 uu____18209
                           else ());
                          (let pat_discriminates uu___28_18234 =
                             match uu___28_18234 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18250;
                                  FStar_Syntax_Syntax.p = uu____18251;_},FStar_Pervasives_Native.None
                                ,uu____18252) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18266;
                                  FStar_Syntax_Syntax.p = uu____18267;_},FStar_Pervasives_Native.None
                                ,uu____18268) -> true
                             | uu____18295 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18398 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18398 with
                                       | (uu____18400,uu____18401,t') ->
                                           let uu____18419 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18419 with
                                            | (FullMatch ,uu____18431) ->
                                                true
                                            | (HeadMatch
                                               uu____18445,uu____18446) ->
                                                true
                                            | uu____18461 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18498 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18498
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18509 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18509 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18597,uu____18598) ->
                                       branches1
                                   | uu____18743 -> branches  in
                                 let uu____18798 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____18807 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____18807 with
                                        | (p,uu____18811,uu____18812) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _18841  -> FStar_Util.Inr _18841)
                                   uu____18798))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____18871 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____18871 with
                                | (p,uu____18880,e) ->
                                    ((let uu____18899 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____18899
                                      then
                                        let uu____18904 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____18906 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____18904 uu____18906
                                      else ());
                                     (let uu____18911 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _18926  -> FStar_Util.Inr _18926)
                                        uu____18911)))))
                 | ((s,t),(uu____18929,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____18932;
                                         FStar_Syntax_Syntax.vars =
                                           uu____18933;_}))
                     ->
                     let uu____19002 =
                       let uu____19004 = is_flex scrutinee  in
                       Prims.op_Negation uu____19004  in
                     if uu____19002
                     then
                       ((let uu____19015 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19015
                         then
                           let uu____19020 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19020
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19039 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19039
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19054 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19054
                           then
                             let uu____19059 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19061 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19059 uu____19061
                           else ());
                          (let pat_discriminates uu___28_19086 =
                             match uu___28_19086 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19102;
                                  FStar_Syntax_Syntax.p = uu____19103;_},FStar_Pervasives_Native.None
                                ,uu____19104) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19118;
                                  FStar_Syntax_Syntax.p = uu____19119;_},FStar_Pervasives_Native.None
                                ,uu____19120) -> true
                             | uu____19147 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19250 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19250 with
                                       | (uu____19252,uu____19253,t') ->
                                           let uu____19271 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19271 with
                                            | (FullMatch ,uu____19283) ->
                                                true
                                            | (HeadMatch
                                               uu____19297,uu____19298) ->
                                                true
                                            | uu____19313 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19350 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19350
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19361 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19361 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19449,uu____19450) ->
                                       branches1
                                   | uu____19595 -> branches  in
                                 let uu____19650 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19659 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19659 with
                                        | (p,uu____19663,uu____19664) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19693  -> FStar_Util.Inr _19693)
                                   uu____19650))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19723 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19723 with
                                | (p,uu____19732,e) ->
                                    ((let uu____19751 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19751
                                      then
                                        let uu____19756 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19758 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19756 uu____19758
                                      else ());
                                     (let uu____19763 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19778  -> FStar_Util.Inr _19778)
                                        uu____19763)))))
                 | uu____19779 ->
                     ((let uu____19801 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____19801
                       then
                         let uu____19806 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____19808 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____19806 uu____19808
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____19854 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____19854
            then
              let uu____19859 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____19861 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____19863 = FStar_Syntax_Print.term_to_string t1  in
              let uu____19865 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____19859 uu____19861 uu____19863 uu____19865
            else ());
           (let uu____19870 = head_matches_delta env1 wl1 t1 t2  in
            match uu____19870 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____19901,uu____19902) ->
                     let rec may_relate head3 =
                       let uu____19930 =
                         let uu____19931 = FStar_Syntax_Subst.compress head3
                            in
                         uu____19931.FStar_Syntax_Syntax.n  in
                       match uu____19930 with
                       | FStar_Syntax_Syntax.Tm_name uu____19935 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____19937 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____19962 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____19962 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____19964 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____19967
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____19968 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____19971,uu____19972) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20014) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20020) ->
                           may_relate t
                       | uu____20025 -> false  in
                     let uu____20027 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20027 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20048 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20048
                          then
                            let uu____20051 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20051 with
                             | (guard,wl2) ->
                                 let uu____20058 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20058)
                          else
                            (let uu____20061 =
                               let uu____20063 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____20065 =
                                 let uu____20067 =
                                   let uu____20071 =
                                     delta_depth_of_term env1 head1  in
                                   FStar_Util.bind_opt uu____20071
                                     (fun x  ->
                                        let uu____20078 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____20078)
                                    in
                                 FStar_Util.dflt "" uu____20067  in
                               let uu____20083 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               let uu____20085 =
                                 let uu____20087 =
                                   let uu____20091 =
                                     delta_depth_of_term env1 head2  in
                                   FStar_Util.bind_opt uu____20091
                                     (fun x  ->
                                        let uu____20098 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____20098)
                                    in
                                 FStar_Util.dflt "" uu____20087  in
                               FStar_Util.format4
                                 "head mismatch (%s (%s) vs %s (%s))"
                                 uu____20063 uu____20065 uu____20083
                                 uu____20085
                                in
                             giveup env1 uu____20061 orig))
                 | (HeadMatch (true ),uu____20104) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20119 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20119 with
                        | (guard,wl2) ->
                            let uu____20126 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20126)
                     else
                       (let uu____20129 =
                          let uu____20131 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____20133 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____20131 uu____20133
                           in
                        giveup env1 uu____20129 orig)
                 | (uu____20136,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2819_20150 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2819_20150.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2819_20150.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2819_20150.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2819_20150.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2819_20150.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2819_20150.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2819_20150.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2819_20150.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20177 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20177
          then
            let uu____20180 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20180
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20186 =
                let uu____20189 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20189  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20186 t1);
             (let uu____20208 =
                let uu____20211 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20211  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20208 t2);
             (let uu____20230 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20230
              then
                let uu____20234 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20236 =
                  let uu____20238 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20240 =
                    let uu____20242 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____20242  in
                  Prims.op_Hat uu____20238 uu____20240  in
                let uu____20245 =
                  let uu____20247 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20249 =
                    let uu____20251 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____20251  in
                  Prims.op_Hat uu____20247 uu____20249  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20234 uu____20236 uu____20245
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20258,uu____20259) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20283,FStar_Syntax_Syntax.Tm_delayed uu____20284) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20308,uu____20309) ->
                  let uu____20336 =
                    let uu___2850_20337 = problem  in
                    let uu____20338 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2850_20337.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20338;
                      FStar_TypeChecker_Common.relation =
                        (uu___2850_20337.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2850_20337.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2850_20337.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2850_20337.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2850_20337.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2850_20337.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2850_20337.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2850_20337.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20336 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20339,uu____20340) ->
                  let uu____20347 =
                    let uu___2856_20348 = problem  in
                    let uu____20349 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2856_20348.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20349;
                      FStar_TypeChecker_Common.relation =
                        (uu___2856_20348.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2856_20348.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2856_20348.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2856_20348.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2856_20348.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2856_20348.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2856_20348.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2856_20348.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20347 wl
              | (uu____20350,FStar_Syntax_Syntax.Tm_ascribed uu____20351) ->
                  let uu____20378 =
                    let uu___2862_20379 = problem  in
                    let uu____20380 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2862_20379.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2862_20379.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2862_20379.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20380;
                      FStar_TypeChecker_Common.element =
                        (uu___2862_20379.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2862_20379.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2862_20379.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2862_20379.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2862_20379.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2862_20379.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20378 wl
              | (uu____20381,FStar_Syntax_Syntax.Tm_meta uu____20382) ->
                  let uu____20389 =
                    let uu___2868_20390 = problem  in
                    let uu____20391 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2868_20390.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2868_20390.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2868_20390.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20391;
                      FStar_TypeChecker_Common.element =
                        (uu___2868_20390.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2868_20390.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2868_20390.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2868_20390.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2868_20390.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2868_20390.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20389 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____20393),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____20395)) ->
                  let uu____20404 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____20404
              | (FStar_Syntax_Syntax.Tm_bvar uu____20405,uu____20406) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____20408,FStar_Syntax_Syntax.Tm_bvar uu____20409) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___29_20479 =
                    match uu___29_20479 with
                    | [] -> c
                    | bs ->
                        let uu____20507 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____20507
                     in
                  let uu____20518 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____20518 with
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
                                    let uu____20667 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____20667
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
                  let mk_t t l uu___30_20756 =
                    match uu___30_20756 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____20798 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____20798 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____20943 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____20944 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____20943
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____20944 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____20946,uu____20947) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____20978 -> true
                    | uu____20998 -> false  in
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
                      (let uu____21058 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___2970_21066 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___2970_21066.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___2970_21066.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___2970_21066.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___2970_21066.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___2970_21066.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___2970_21066.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___2970_21066.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___2970_21066.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___2970_21066.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___2970_21066.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___2970_21066.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___2970_21066.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___2970_21066.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___2970_21066.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___2970_21066.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___2970_21066.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___2970_21066.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___2970_21066.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___2970_21066.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___2970_21066.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___2970_21066.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___2970_21066.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___2970_21066.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___2970_21066.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___2970_21066.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___2970_21066.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___2970_21066.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___2970_21066.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___2970_21066.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___2970_21066.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___2970_21066.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___2970_21066.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                (uu___2967_21047.FStar_TypeChecker_Env.synth_hook);
=======
                                (uu___2973_21094.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___2973_21094.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> cp debugging an issue
=======
                                (uu___2967_21047.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___2967_21047.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> some more comments
=======
                                (uu___2970_21066.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___2970_21066.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
                              FStar_TypeChecker_Env.splice =
                                (uu___2970_21066.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___2970_21066.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___2970_21066.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___2970_21066.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___2970_21066.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___2970_21066.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___2970_21066.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___2970_21066.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___2970_21066.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21058 with
                       | (uu____21071,ty,uu____21073) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21082 =
                                 let uu____21083 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21083.FStar_Syntax_Syntax.n  in
                               match uu____21082 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21086 ->
                                   let uu____21093 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21093
                               | uu____21094 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21097 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21097
                             then
                               let uu____21102 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21104 =
                                 let uu____21106 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21106
                                  in
                               let uu____21107 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21102 uu____21104 uu____21107
                             else ());
                            r1))
                     in
                  let uu____21112 =
                    let uu____21129 = maybe_eta t1  in
                    let uu____21136 = maybe_eta t2  in
                    (uu____21129, uu____21136)  in
                  (match uu____21112 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___2991_21178 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___2991_21178.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___2991_21178.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___2991_21178.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___2991_21178.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___2991_21178.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___2991_21178.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___2991_21178.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___2991_21178.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21199 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21199
                       then
                         let uu____21202 = destruct_flex_t not_abs wl  in
                         (match uu____21202 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3008_21219 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3008_21219.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3008_21219.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3008_21219.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3008_21219.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3008_21219.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3008_21219.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3008_21219.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3008_21219.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21243 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21243
                       then
                         let uu____21246 = destruct_flex_t not_abs wl  in
                         (match uu____21246 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3008_21263 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3008_21263.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3008_21263.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3008_21263.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3008_21263.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3008_21263.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3008_21263.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3008_21263.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3008_21263.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____21267 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21285,FStar_Syntax_Syntax.Tm_abs uu____21286) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21317 -> true
                    | uu____21337 -> false  in
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
                      (let uu____21397 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___2970_21405 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___2970_21405.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___2970_21405.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___2970_21405.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___2970_21405.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___2970_21405.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___2970_21405.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___2970_21405.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___2970_21405.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___2970_21405.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___2970_21405.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___2970_21405.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___2970_21405.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___2970_21405.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___2970_21405.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___2970_21405.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___2970_21405.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___2970_21405.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___2970_21405.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___2970_21405.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___2970_21405.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___2970_21405.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___2970_21405.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___2970_21405.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___2970_21405.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___2970_21405.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___2970_21405.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___2970_21405.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___2970_21405.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___2970_21405.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___2970_21405.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___2970_21405.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___2970_21405.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                (uu___2967_21386.FStar_TypeChecker_Env.synth_hook);
=======
                                (uu___2973_21433.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___2973_21433.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> cp debugging an issue
=======
                                (uu___2967_21386.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___2967_21386.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> some more comments
=======
                                (uu___2970_21405.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___2970_21405.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
                              FStar_TypeChecker_Env.splice =
                                (uu___2970_21405.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___2970_21405.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___2970_21405.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___2970_21405.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___2970_21405.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___2970_21405.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___2970_21405.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___2970_21405.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___2970_21405.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21397 with
                       | (uu____21410,ty,uu____21412) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21421 =
                                 let uu____21422 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21422.FStar_Syntax_Syntax.n  in
                               match uu____21421 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21425 ->
                                   let uu____21432 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21432
                               | uu____21433 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21436 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21436
                             then
                               let uu____21441 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21443 =
                                 let uu____21445 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21445
                                  in
                               let uu____21446 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21441 uu____21443 uu____21446
                             else ());
                            r1))
                     in
                  let uu____21451 =
                    let uu____21468 = maybe_eta t1  in
                    let uu____21475 = maybe_eta t2  in
                    (uu____21468, uu____21475)  in
                  (match uu____21451 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___2991_21517 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___2991_21517.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___2991_21517.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___2991_21517.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___2991_21517.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___2991_21517.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___2991_21517.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___2991_21517.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___2991_21517.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21538 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21538
                       then
                         let uu____21541 = destruct_flex_t not_abs wl  in
                         (match uu____21541 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3008_21558 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3008_21558.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3008_21558.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3008_21558.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3008_21558.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3008_21558.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3008_21558.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3008_21558.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3008_21558.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21582 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21582
                       then
                         let uu____21585 = destruct_flex_t not_abs wl  in
                         (match uu____21585 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3008_21602 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3008_21602.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3008_21602.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3008_21602.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3008_21602.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3008_21602.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3008_21602.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3008_21602.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3008_21602.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____21606 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____21636 =
                    let uu____21641 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____21641 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3031_21669 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3031_21669.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3031_21669.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3033_21671 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3033_21671.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3033_21671.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____21672,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3031_21687 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3031_21687.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3031_21687.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3033_21689 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3033_21689.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3033_21689.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____21690 -> (x1, x2)  in
                  (match uu____21636 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____21709 = as_refinement false env t11  in
                       (match uu____21709 with
                        | (x12,phi11) ->
                            let uu____21717 = as_refinement false env t21  in
                            (match uu____21717 with
                             | (x22,phi21) ->
                                 ((let uu____21726 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21726
                                   then
                                     ((let uu____21731 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____21733 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21735 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____21731
                                         uu____21733 uu____21735);
                                      (let uu____21738 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____21740 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21742 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____21738
                                         uu____21740 uu____21742))
                                   else ());
                                  (let uu____21747 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____21747 with
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
                                         let uu____21818 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____21818
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____21830 =
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
                                         (let uu____21843 =
                                            let uu____21846 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____21846
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____21843
                                            (p_guard base_prob));
                                         (let uu____21865 =
                                            let uu____21868 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____21868
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____21865
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____21887 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____21887)
                                          in
                                       let has_uvars =
                                         (let uu____21892 =
                                            let uu____21894 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____21894
                                             in
                                          Prims.op_Negation uu____21892) ||
                                           (let uu____21898 =
                                              let uu____21900 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____21900
                                               in
                                            Prims.op_Negation uu____21898)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____21904 =
                                           let uu____21909 =
                                             let uu____21918 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____21918]  in
                                           mk_t_problem wl1 uu____21909 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____21904 with
                                          | (ref_prob,wl2) ->
                                              let uu____21940 =
                                                solve env1
                                                  (let uu___3075_21942 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3075_21942.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3075_21942.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3075_21942.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3075_21942.tcenv);
                                                     wl_implicits =
                                                       (uu___3075_21942.wl_implicits)
                                                   })
                                                 in
                                              (match uu____21940 with
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
                                               | Success uu____21959 ->
                                                   let guard =
                                                     let uu____21967 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____21967
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___3086_21976 =
                                                       wl3  in
                                                     {
                                                       attempting =
                                                         (uu___3086_21976.attempting);
                                                       wl_deferred =
                                                         (uu___3086_21976.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            Prims.int_one);
                                                       defer_ok =
                                                         (uu___3086_21976.defer_ok);
                                                       smt_ok =
                                                         (uu___3086_21976.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___3086_21976.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___3086_21976.tcenv);
                                                       wl_implicits =
                                                         (uu___3086_21976.wl_implicits)
                                                     }  in
                                                   let uu____21978 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____21978))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____21981,FStar_Syntax_Syntax.Tm_uvar uu____21982) ->
                  let uu____22007 = destruct_flex_t t1 wl  in
                  (match uu____22007 with
                   | (f1,wl1) ->
                       let uu____22014 = destruct_flex_t t2 wl1  in
                       (match uu____22014 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22021;
                    FStar_Syntax_Syntax.pos = uu____22022;
                    FStar_Syntax_Syntax.vars = uu____22023;_},uu____22024),FStar_Syntax_Syntax.Tm_uvar
                 uu____22025) ->
                  let uu____22074 = destruct_flex_t t1 wl  in
                  (match uu____22074 with
                   | (f1,wl1) ->
                       let uu____22081 = destruct_flex_t t2 wl1  in
                       (match uu____22081 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22088,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22089;
                    FStar_Syntax_Syntax.pos = uu____22090;
                    FStar_Syntax_Syntax.vars = uu____22091;_},uu____22092))
                  ->
                  let uu____22141 = destruct_flex_t t1 wl  in
                  (match uu____22141 with
                   | (f1,wl1) ->
                       let uu____22148 = destruct_flex_t t2 wl1  in
                       (match uu____22148 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22155;
                    FStar_Syntax_Syntax.pos = uu____22156;
                    FStar_Syntax_Syntax.vars = uu____22157;_},uu____22158),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22159;
                    FStar_Syntax_Syntax.pos = uu____22160;
                    FStar_Syntax_Syntax.vars = uu____22161;_},uu____22162))
                  ->
                  let uu____22235 = destruct_flex_t t1 wl  in
                  (match uu____22235 with
                   | (f1,wl1) ->
                       let uu____22242 = destruct_flex_t t2 wl1  in
                       (match uu____22242 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22249,uu____22250) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22263 = destruct_flex_t t1 wl  in
                  (match uu____22263 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22270;
                    FStar_Syntax_Syntax.pos = uu____22271;
                    FStar_Syntax_Syntax.vars = uu____22272;_},uu____22273),uu____22274)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22311 = destruct_flex_t t1 wl  in
                  (match uu____22311 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22318,FStar_Syntax_Syntax.Tm_uvar uu____22319) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22332,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22333;
                    FStar_Syntax_Syntax.pos = uu____22334;
                    FStar_Syntax_Syntax.vars = uu____22335;_},uu____22336))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22373,FStar_Syntax_Syntax.Tm_arrow uu____22374) ->
                  solve_t' env
                    (let uu___3186_22402 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3186_22402.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3186_22402.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3186_22402.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3186_22402.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3186_22402.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3186_22402.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3186_22402.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3186_22402.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3186_22402.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22403;
                    FStar_Syntax_Syntax.pos = uu____22404;
                    FStar_Syntax_Syntax.vars = uu____22405;_},uu____22406),FStar_Syntax_Syntax.Tm_arrow
                 uu____22407) ->
                  solve_t' env
                    (let uu___3186_22459 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3186_22459.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3186_22459.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3186_22459.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3186_22459.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3186_22459.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3186_22459.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3186_22459.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3186_22459.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3186_22459.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22460,FStar_Syntax_Syntax.Tm_uvar uu____22461) ->
                  let uu____22474 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22474
              | (uu____22475,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22476;
                    FStar_Syntax_Syntax.pos = uu____22477;
                    FStar_Syntax_Syntax.vars = uu____22478;_},uu____22479))
                  ->
                  let uu____22516 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22516
              | (FStar_Syntax_Syntax.Tm_uvar uu____22517,uu____22518) ->
                  let uu____22531 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22531
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22532;
                    FStar_Syntax_Syntax.pos = uu____22533;
                    FStar_Syntax_Syntax.vars = uu____22534;_},uu____22535),uu____22536)
                  ->
                  let uu____22573 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22573
              | (FStar_Syntax_Syntax.Tm_refine uu____22574,uu____22575) ->
                  let t21 =
                    let uu____22583 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____22583  in
                  solve_t env
                    (let uu___3221_22609 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3221_22609.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3221_22609.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3221_22609.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3221_22609.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3221_22609.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3221_22609.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3221_22609.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3221_22609.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3221_22609.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22610,FStar_Syntax_Syntax.Tm_refine uu____22611) ->
                  let t11 =
                    let uu____22619 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22619  in
                  solve_t env
                    (let uu___3228_22645 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3228_22645.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3228_22645.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3228_22645.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3228_22645.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3228_22645.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3228_22645.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3228_22645.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3228_22645.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3228_22645.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____22727 =
                    let uu____22728 = guard_of_prob env wl problem t1 t2  in
                    match uu____22728 with
                    | (guard,wl1) ->
                        let uu____22735 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____22735
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____22954 = br1  in
                        (match uu____22954 with
                         | (p1,w1,uu____22983) ->
                             let uu____23000 = br2  in
                             (match uu____23000 with
                              | (p2,w2,uu____23023) ->
                                  let uu____23028 =
                                    let uu____23030 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23030  in
                                  if uu____23028
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23057 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23057 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23094 = br2  in
                                         (match uu____23094 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23127 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23127
                                                 in
                                              let uu____23132 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23163,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23184) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23243 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23243 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23132
                                                (fun uu____23315  ->
                                                   match uu____23315 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23352 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23352
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____23373
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____23373
                                                              then
                                                                let uu____23378
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____23380
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____23378
                                                                  uu____23380
                                                              else ());
                                                             (let uu____23386
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____23386
                                                                (fun
                                                                   uu____23422
                                                                    ->
                                                                   match uu____23422
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
                    | uu____23551 -> FStar_Pervasives_Native.None  in
                  let uu____23592 = solve_branches wl brs1 brs2  in
                  (match uu____23592 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____23643 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____23643 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____23677 =
                                FStar_List.map
                                  (fun uu____23689  ->
                                     match uu____23689 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____23677  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____23698 =
                              let uu____23699 =
                                let uu____23700 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____23700
                                  (let uu___3327_23708 = wl3  in
                                   {
                                     attempting =
                                       (uu___3327_23708.attempting);
                                     wl_deferred =
                                       (uu___3327_23708.wl_deferred);
                                     ctr = (uu___3327_23708.ctr);
                                     defer_ok = (uu___3327_23708.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3327_23708.umax_heuristic_ok);
                                     tcenv = (uu___3327_23708.tcenv);
                                     wl_implicits =
                                       (uu___3327_23708.wl_implicits)
                                   })
                                 in
                              solve env uu____23699  in
                            (match uu____23698 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____23713 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____23720,uu____23721) ->
                  let head1 =
                    let uu____23745 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23745
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23791 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23791
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23837 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23837
                    then
                      let uu____23841 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23843 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23845 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23841 uu____23843 uu____23845
                    else ());
                   (let no_free_uvars t =
                      (let uu____23859 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23859) &&
                        (let uu____23863 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23863)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____23880 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23880 = FStar_Syntax_Util.Equal  in
                    let uu____23881 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23881
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23885 = equal t1 t2  in
                         (if uu____23885
                          then
                            let uu____23888 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____23888
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23893 =
                            let uu____23900 = equal t1 t2  in
                            if uu____23900
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23913 = mk_eq2 wl env orig t1 t2  in
                               match uu____23913 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____23893 with
                          | (guard,wl1) ->
                              let uu____23934 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____23934))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____23937,uu____23938) ->
                  let head1 =
                    let uu____23946 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23946
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23992 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23992
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24038 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24038
                    then
                      let uu____24042 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24044 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24046 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24042 uu____24044 uu____24046
                    else ());
                   (let no_free_uvars t =
                      (let uu____24060 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24060) &&
                        (let uu____24064 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24064)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24081 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24081 = FStar_Syntax_Util.Equal  in
                    let uu____24082 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24082
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24086 = equal t1 t2  in
                         (if uu____24086
                          then
                            let uu____24089 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24089
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24094 =
                            let uu____24101 = equal t1 t2  in
                            if uu____24101
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24114 = mk_eq2 wl env orig t1 t2  in
                               match uu____24114 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24094 with
                          | (guard,wl1) ->
                              let uu____24135 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24135))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24138,uu____24139) ->
                  let head1 =
                    let uu____24141 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24141
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24187 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24187
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24233 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24233
                    then
                      let uu____24237 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24239 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24241 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24237 uu____24239 uu____24241
                    else ());
                   (let no_free_uvars t =
                      (let uu____24255 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24255) &&
                        (let uu____24259 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24259)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24276 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24276 = FStar_Syntax_Util.Equal  in
                    let uu____24277 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24277
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24281 = equal t1 t2  in
                         (if uu____24281
                          then
                            let uu____24284 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24284
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24289 =
                            let uu____24296 = equal t1 t2  in
                            if uu____24296
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24309 = mk_eq2 wl env orig t1 t2  in
                               match uu____24309 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24289 with
                          | (guard,wl1) ->
                              let uu____24330 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24330))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24333,uu____24334) ->
                  let head1 =
                    let uu____24336 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24336
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24382 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24382
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24428 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24428
                    then
                      let uu____24432 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24434 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24436 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24432 uu____24434 uu____24436
                    else ());
                   (let no_free_uvars t =
                      (let uu____24450 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24450) &&
                        (let uu____24454 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24454)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24471 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24471 = FStar_Syntax_Util.Equal  in
                    let uu____24472 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24472
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24476 = equal t1 t2  in
                         (if uu____24476
                          then
                            let uu____24479 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24479
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24484 =
                            let uu____24491 = equal t1 t2  in
                            if uu____24491
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24504 = mk_eq2 wl env orig t1 t2  in
                               match uu____24504 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24484 with
                          | (guard,wl1) ->
                              let uu____24525 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24525))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____24528,uu____24529) ->
                  let head1 =
                    let uu____24531 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24531
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24577 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24577
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24623 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24623
                    then
                      let uu____24627 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24629 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24631 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24627 uu____24629 uu____24631
                    else ());
                   (let no_free_uvars t =
                      (let uu____24645 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24645) &&
                        (let uu____24649 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24649)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
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
              | (FStar_Syntax_Syntax.Tm_app uu____24723,uu____24724) ->
                  let head1 =
                    let uu____24742 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24742
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24788 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24788
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24834 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24834
                    then
                      let uu____24838 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24840 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24842 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24838 uu____24840 uu____24842
                    else ());
                   (let no_free_uvars t =
                      (let uu____24856 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24856) &&
                        (let uu____24860 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24860)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24877 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24877 = FStar_Syntax_Util.Equal  in
                    let uu____24878 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24878
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24882 = equal t1 t2  in
                         (if uu____24882
                          then
                            let uu____24885 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24885
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24890 =
                            let uu____24897 = equal t1 t2  in
                            if uu____24897
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24910 = mk_eq2 wl env orig t1 t2  in
                               match uu____24910 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24890 with
                          | (guard,wl1) ->
                              let uu____24931 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24931))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24934,FStar_Syntax_Syntax.Tm_match uu____24935) ->
                  let head1 =
                    let uu____24959 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24959
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25005 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25005
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25051 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25051
                    then
                      let uu____25055 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25057 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25059 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25055 uu____25057 uu____25059
                    else ());
                   (let no_free_uvars t =
                      (let uu____25073 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25073) &&
                        (let uu____25077 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25077)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25094 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25094 = FStar_Syntax_Util.Equal  in
                    let uu____25095 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25095
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25099 = equal t1 t2  in
                         (if uu____25099
                          then
                            let uu____25102 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25102
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25107 =
                            let uu____25114 = equal t1 t2  in
                            if uu____25114
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25127 = mk_eq2 wl env orig t1 t2  in
                               match uu____25127 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25107 with
                          | (guard,wl1) ->
                              let uu____25148 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25148))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25151,FStar_Syntax_Syntax.Tm_uinst uu____25152) ->
                  let head1 =
                    let uu____25160 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25160
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25200 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25200
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25240 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25240
                    then
                      let uu____25244 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25246 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25248 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25244 uu____25246 uu____25248
                    else ());
                   (let no_free_uvars t =
                      (let uu____25262 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25262) &&
                        (let uu____25266 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25266)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25283 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25283 = FStar_Syntax_Util.Equal  in
                    let uu____25284 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25284
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25288 = equal t1 t2  in
                         (if uu____25288
                          then
                            let uu____25291 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25291
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25296 =
                            let uu____25303 = equal t1 t2  in
                            if uu____25303
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25316 = mk_eq2 wl env orig t1 t2  in
                               match uu____25316 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25296 with
                          | (guard,wl1) ->
                              let uu____25337 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25337))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25340,FStar_Syntax_Syntax.Tm_name uu____25341) ->
                  let head1 =
                    let uu____25343 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25343
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25383 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25383
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25423 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25423
                    then
                      let uu____25427 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25429 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25431 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25427 uu____25429 uu____25431
                    else ());
                   (let no_free_uvars t =
                      (let uu____25445 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25445) &&
                        (let uu____25449 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25449)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25466 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25466 = FStar_Syntax_Util.Equal  in
                    let uu____25467 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25467
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25471 = equal t1 t2  in
                         (if uu____25471
                          then
                            let uu____25474 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25474
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25479 =
                            let uu____25486 = equal t1 t2  in
                            if uu____25486
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25499 = mk_eq2 wl env orig t1 t2  in
                               match uu____25499 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25479 with
                          | (guard,wl1) ->
                              let uu____25520 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25520))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25523,FStar_Syntax_Syntax.Tm_constant uu____25524) ->
                  let head1 =
                    let uu____25526 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25526
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25566 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25566
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25606 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25606
                    then
                      let uu____25610 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25612 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25614 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25610 uu____25612 uu____25614
                    else ());
                   (let no_free_uvars t =
                      (let uu____25628 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25628) &&
                        (let uu____25632 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25632)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25649 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25649 = FStar_Syntax_Util.Equal  in
                    let uu____25650 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25650
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25654 = equal t1 t2  in
                         (if uu____25654
                          then
                            let uu____25657 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25657
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25662 =
                            let uu____25669 = equal t1 t2  in
                            if uu____25669
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25682 = mk_eq2 wl env orig t1 t2  in
                               match uu____25682 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25662 with
                          | (guard,wl1) ->
                              let uu____25703 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25703))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25706,FStar_Syntax_Syntax.Tm_fvar uu____25707) ->
                  let head1 =
                    let uu____25709 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25709
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25749 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25749
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25789 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25789
                    then
                      let uu____25793 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25795 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25797 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25793 uu____25795 uu____25797
                    else ());
                   (let no_free_uvars t =
                      (let uu____25811 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25811) &&
                        (let uu____25815 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25815)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25832 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25832 = FStar_Syntax_Util.Equal  in
                    let uu____25833 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25833
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25837 = equal t1 t2  in
                         (if uu____25837
                          then
                            let uu____25840 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25840
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25845 =
                            let uu____25852 = equal t1 t2  in
                            if uu____25852
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25865 = mk_eq2 wl env orig t1 t2  in
                               match uu____25865 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25845 with
                          | (guard,wl1) ->
                              let uu____25886 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25886))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25889,FStar_Syntax_Syntax.Tm_app uu____25890) ->
                  let head1 =
                    let uu____25908 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25908
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25948 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25948
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25988 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25988
                    then
                      let uu____25992 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25994 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25996 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25992 uu____25994 uu____25996
                    else ());
                   (let no_free_uvars t =
                      (let uu____26010 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26010) &&
                        (let uu____26014 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26014)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____26031 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26031 = FStar_Syntax_Util.Equal  in
                    let uu____26032 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26032
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26036 = equal t1 t2  in
                         (if uu____26036
                          then
                            let uu____26039 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26039
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26044 =
                            let uu____26051 = equal t1 t2  in
                            if uu____26051
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26064 = mk_eq2 wl env orig t1 t2  in
                               match uu____26064 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26044 with
                          | (guard,wl1) ->
                              let uu____26085 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26085))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26088,FStar_Syntax_Syntax.Tm_let uu____26089) ->
                  let uu____26116 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26116
                  then
                    let uu____26119 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26119
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____26123,uu____26124) ->
                  let uu____26138 =
                    let uu____26144 =
                      let uu____26146 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26148 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26150 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26152 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26146 uu____26148 uu____26150 uu____26152
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26144)
                     in
                  FStar_Errors.raise_error uu____26138
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26156,FStar_Syntax_Syntax.Tm_let uu____26157) ->
                  let uu____26171 =
                    let uu____26177 =
                      let uu____26179 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26181 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26183 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26185 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26179 uu____26181 uu____26183 uu____26185
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26177)
                     in
                  FStar_Errors.raise_error uu____26171
                    t1.FStar_Syntax_Syntax.pos
              | uu____26189 -> giveup env "head tag mismatch" orig))))

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
          (let uu____26258 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26258
           then
             let uu____26263 =
               let uu____26265 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26265  in
             let uu____26266 =
               let uu____26268 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26268  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26263 uu____26266
           else ());
          (let uu____26272 =
             let uu____26274 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26274  in
           if uu____26272
           then
             let uu____26277 =
               let uu____26279 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____26281 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____26279 uu____26281
                in
             giveup env uu____26277 orig
           else
<<<<<<< HEAD
             (let uu____26267 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____26267 with
              | (ret_sub_prob,wl1) ->
                  let uu____26275 =
                    FStar_List.fold_right2
                      (fun uu____26312  ->
                         fun uu____26313  ->
                           fun uu____26314  ->
                             match (uu____26312, uu____26313, uu____26314)
                             with
                             | ((a1,uu____26358),(a2,uu____26360),(arg_sub_probs,wl2))
                                 ->
                                 let uu____26393 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____26393 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
=======
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
<<<<<<< HEAD
               (let uu____26279 =
                  let uu____26281 =
=======
               (let uu____26303 =
                  let uu____26305 =
>>>>>>> snap
                    FStar_Syntax_Print.args_to_string
>>>>>>> snap
                      c1_comp.FStar_Syntax_Syntax.effect_args
                     in
<<<<<<< HEAD
<<<<<<< HEAD
                  (match uu____26275 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs =
                         let uu____26420 =
                           let uu____26423 =
                             FStar_All.pipe_right
                               g_lift.FStar_TypeChecker_Common.deferred
                               (FStar_List.map FStar_Pervasives_Native.snd)
                              in
                           FStar_List.append arg_sub_probs uu____26423  in
                         ret_sub_prob :: uu____26420  in
                       let guard =
                         let guard =
                           let uu____26445 = FStar_List.map p_guard sub_probs
                              in
                           FStar_Syntax_Util.mk_conj_l uu____26445  in
                         match g_lift.FStar_TypeChecker_Common.guard_f with
                         | FStar_TypeChecker_Common.Trivial  -> guard
                         | FStar_TypeChecker_Common.NonTrivial f ->
                             FStar_Syntax_Util.mk_conj guard f
                          in
                       let wl3 =
                         let uu___3461_26454 = wl2  in
                         {
                           attempting = (uu___3461_26454.attempting);
                           wl_deferred = (uu___3461_26454.wl_deferred);
                           ctr = (uu___3461_26454.ctr);
                           defer_ok = (uu___3461_26454.defer_ok);
                           smt_ok = (uu___3461_26454.smt_ok);
                           umax_heuristic_ok =
                             (uu___3461_26454.umax_heuristic_ok);
                           tcenv = (uu___3461_26454.tcenv);
                           wl_implicits =
                             (FStar_List.append
                                g_lift.FStar_TypeChecker_Common.implicits
                                wl2.wl_implicits)
                         }  in
                       let wl4 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl3
                          in
                       let uu____26456 = attempt sub_probs wl4  in
                       solve env uu____26456)))
=======
                  let uu____26307 =
                    FStar_Syntax_Print.args_to_string
                      c2_comp.FStar_Syntax_Syntax.effect_args
                     in
                  FStar_Util.format2
                    "incompatible effect arguments: %s <> %s" uu____26305
                    uu____26307
                   in
                giveup env uu____26303 orig)
             else
               (let uu____26312 =
                  sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                    FStar_TypeChecker_Common.EQ
                    c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                   in
                match uu____26312 with
                | (ret_sub_prob,wl1) ->
                    let uu____26320 =
                      FStar_List.fold_right2
                        (fun uu____26357  ->
                           fun uu____26358  ->
                             fun uu____26359  ->
                               match (uu____26357, uu____26358, uu____26359)
                               with
                               | ((a1,uu____26403),(a2,uu____26405),(arg_sub_probs,wl2))
                                   ->
                                   let uu____26438 =
                                     sub_prob wl2 a1
                                       FStar_TypeChecker_Common.EQ a2
                                       "effect arg"
                                      in
                                   (match uu____26438 with
                                    | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                        c1_comp.FStar_Syntax_Syntax.effect_args
                        c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                       in
                    (match uu____26320 with
                     | (arg_sub_probs,wl2) ->
                         let sub_probs =
                           let uu____26465 =
                             let uu____26468 =
                               FStar_All.pipe_right
                                 g_lift.FStar_TypeChecker_Common.deferred
                                 (FStar_List.map FStar_Pervasives_Native.snd)
                                in
                             FStar_List.append arg_sub_probs uu____26468  in
                           ret_sub_prob :: uu____26465  in
                         let guard =
                           let guard =
                             let uu____26490 =
                               FStar_List.map p_guard sub_probs  in
                             FStar_Syntax_Util.mk_conj_l uu____26490  in
                           match g_lift.FStar_TypeChecker_Common.guard_f with
                           | FStar_TypeChecker_Common.Trivial  -> guard
                           | FStar_TypeChecker_Common.NonTrivial f ->
                               FStar_Syntax_Util.mk_conj guard f
                            in
                         let wl3 =
                           let uu___3465_26499 = wl2  in
                           {
                             attempting = (uu___3465_26499.attempting);
                             wl_deferred = (uu___3465_26499.wl_deferred);
                             ctr = (uu___3465_26499.ctr);
                             defer_ok = (uu___3465_26499.defer_ok);
                             smt_ok = (uu___3465_26499.smt_ok);
                             umax_heuristic_ok =
                               (uu___3465_26499.umax_heuristic_ok);
                             tcenv = (uu___3465_26499.tcenv);
                             wl_implicits =
                               (FStar_List.append
                                  g_lift.FStar_TypeChecker_Common.implicits
                                  wl2.wl_implicits)
                           }  in
                         let wl4 =
                           solve_prob orig
                             (FStar_Pervasives_Native.Some guard) [] wl3
                            in
                         let uu____26501 = attempt sub_probs wl4  in
                         solve env uu____26501)))
>>>>>>> snap
           in
        let solve_layered_sub c11 edge c21 =
          (let supported =
             ((FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
                 c21.FStar_Syntax_Syntax.effect_name)
                &&
                (FStar_TypeChecker_Env.is_layered_effect env
                   c11.FStar_Syntax_Syntax.effect_name))
               ||
               ((FStar_TypeChecker_Env.is_layered_effect env
                   c21.FStar_Syntax_Syntax.effect_name)
                  &&
<<<<<<< HEAD
                  (let uu____26477 =
                     FStar_TypeChecker_Env.is_layered_effect env
                       c11.FStar_Syntax_Syntax.effect_name
                      in
                   Prims.op_Negation uu____26477))
              in
           if Prims.op_Negation supported
           then
             let uu____26481 =
               let uu____26483 =
                 let uu____26485 =
                   FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
                 FStar_All.pipe_right uu____26485
                   FStar_Syntax_Print.comp_to_string
                  in
               let uu____26487 =
                 let uu____26489 =
                   FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
                 FStar_All.pipe_right uu____26489
=======
                  (let uu____26522 =
                     FStar_TypeChecker_Env.is_layered_effect env
                       c11.FStar_Syntax_Syntax.effect_name
                      in
                   Prims.op_Negation uu____26522))
              in
           if Prims.op_Negation supported
           then
             let uu____26526 =
               let uu____26528 =
                 let uu____26530 =
                   FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
                 FStar_All.pipe_right uu____26530
                   FStar_Syntax_Print.comp_to_string
                  in
               let uu____26532 =
                 let uu____26534 =
                   FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
                 FStar_All.pipe_right uu____26534
>>>>>>> snap
                   FStar_Syntax_Print.comp_to_string
                  in
               FStar_Util.format2
                 "Unsupported case for solve_layered_sub c1: %s and c2: %s"
<<<<<<< HEAD
                 uu____26483 uu____26487
                in
             failwith uu____26481
           else ());
          (let uu____26495 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____26495
           then
             let uu____26500 =
               let uu____26502 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26502
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____26504 =
               let uu____26506 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26506
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____26500 uu____26504
           else ());
          (let uu____26511 =
             let uu____26516 =
               let uu____26521 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26521
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____26516
               (fun uu____26538  ->
                  match uu____26538 with
                  | (c,g) ->
                      let uu____26549 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____26549, g))
              in
           match uu____26511 with
           | (c12,g_lift) ->
               ((let uu____26553 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____26553
                 then
                   let uu____26558 =
                     let uu____26560 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26560
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____26562 =
                     let uu____26564 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26564
=======
                 uu____26528 uu____26532
                in
             failwith uu____26526
           else ());
          (let uu____26540 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____26540
           then
             let uu____26545 =
               let uu____26547 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26547
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____26549 =
               let uu____26551 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26551
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____26545 uu____26549
           else ());
          (let uu____26556 =
             let uu____26561 =
               let uu____26566 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26566
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____26561
               (fun uu____26583  ->
                  match uu____26583 with
                  | (c,g) ->
                      let uu____26594 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____26594, g))
              in
           match uu____26556 with
           | (c12,g_lift) ->
               ((let uu____26598 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____26598
                 then
                   let uu____26603 =
                     let uu____26605 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26605
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____26607 =
                     let uu____26609 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26609
>>>>>>> snap
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
<<<<<<< HEAD
                     uu____26558 uu____26562
=======
                     uu____26603 uu____26607
>>>>>>> snap
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
<<<<<<< HEAD
                     let uu___3485_26574 = wl  in
                     {
                       attempting = (uu___3485_26574.attempting);
                       wl_deferred = (uu___3485_26574.wl_deferred);
                       ctr = (uu___3485_26574.ctr);
                       defer_ok = (uu___3485_26574.defer_ok);
                       smt_ok = (uu___3485_26574.smt_ok);
                       umax_heuristic_ok =
                         (uu___3485_26574.umax_heuristic_ok);
                       tcenv = (uu___3485_26574.tcenv);
=======
                     let uu___3489_26619 = wl  in
                     {
                       attempting = (uu___3489_26619.attempting);
                       wl_deferred = (uu___3489_26619.wl_deferred);
                       ctr = (uu___3489_26619.ctr);
                       defer_ok = (uu___3489_26619.defer_ok);
                       smt_ok = (uu___3489_26619.smt_ok);
                       umax_heuristic_ok =
                         (uu___3489_26619.umax_heuristic_ok);
                       tcenv = (uu___3489_26619.tcenv);
>>>>>>> snap
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
<<<<<<< HEAD
                   let uu____26575 =
                     let is_uvar1 t =
                       let uu____26589 =
                         let uu____26590 = FStar_Syntax_Subst.compress t  in
                         uu____26590.FStar_Syntax_Syntax.n  in
                       match uu____26589 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____26594 -> true
                       | FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_uvar uu____26608;
                              FStar_Syntax_Syntax.pos = uu____26609;
                              FStar_Syntax_Syntax.vars = uu____26610;_},uu____26611)
=======
                   let uu____26620 =
                     let is_uvar1 t =
                       let uu____26634 =
                         let uu____26635 = FStar_Syntax_Subst.compress t  in
                         uu____26635.FStar_Syntax_Syntax.n  in
                       match uu____26634 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____26639 -> true
                       | FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_uvar uu____26653;
                              FStar_Syntax_Syntax.pos = uu____26654;
                              FStar_Syntax_Syntax.vars = uu____26655;_},uu____26656)
>>>>>>> snap
                           -> true
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
<<<<<<< HEAD
                                FStar_Syntax_Syntax.Tm_uvar uu____26629;
                              FStar_Syntax_Syntax.pos = uu____26630;
                              FStar_Syntax_Syntax.vars = uu____26631;_},uu____26632)
                           -> true
                       | uu____26670 -> false  in
                     FStar_List.fold_right2
                       (fun uu____26703  ->
                          fun uu____26704  ->
                            fun uu____26705  ->
                              match (uu____26703, uu____26704, uu____26705)
                              with
                              | ((a1,uu____26749),(a2,uu____26751),(is_sub_probs,wl2))
                                  ->
                                  let uu____26784 = is_uvar1 a1  in
                                  if uu____26784
                                  then
                                    let uu____26793 =
=======
                                FStar_Syntax_Syntax.Tm_uvar uu____26674;
                              FStar_Syntax_Syntax.pos = uu____26675;
                              FStar_Syntax_Syntax.vars = uu____26676;_},uu____26677)
                           -> true
                       | uu____26715 -> false  in
                     FStar_List.fold_right2
                       (fun uu____26748  ->
                          fun uu____26749  ->
                            fun uu____26750  ->
                              match (uu____26748, uu____26749, uu____26750)
                              with
                              | ((a1,uu____26794),(a2,uu____26796),(is_sub_probs,wl2))
                                  ->
                                  let uu____26829 = is_uvar1 a1  in
                                  if uu____26829
                                  then
                                    let uu____26838 =
>>>>>>> snap
                                      sub_prob wl2 a1
                                        FStar_TypeChecker_Common.EQ a2
                                        "l.h.s. effect index uvar"
                                       in
<<<<<<< HEAD
                                    (match uu____26793 with
=======
                                    (match uu____26838 with
>>>>>>> snap
                                     | (p,wl3) -> ((p :: is_sub_probs), wl3))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
<<<<<<< HEAD
                   match uu____26575 with
                   | (is_sub_probs,wl2) ->
                       let uu____26821 =
=======
                   match uu____26620 with
                   | (is_sub_probs,wl2) ->
                       let uu____26866 =
>>>>>>> snap
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
<<<<<<< HEAD
                       (match uu____26821 with
                        | (ret_sub_prob,wl3) ->
                            let uu____26829 =
                              let uu____26834 =
=======
                       (match uu____26866 with
                        | (ret_sub_prob,wl3) ->
                            let uu____26874 =
                              let uu____26879 =
>>>>>>> snap
                                FStar_All.pipe_right
                                  c21.FStar_Syntax_Syntax.effect_name
                                  (FStar_TypeChecker_Env.get_effect_decl env)
                                 in
<<<<<<< HEAD
                              FStar_All.pipe_right uu____26834
=======
                              FStar_All.pipe_right uu____26879
>>>>>>> snap
                                (fun ed  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with
                                     ed.FStar_Syntax_Syntax.stronger
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
<<<<<<< HEAD
                            (match uu____26829 with
                             | (uu____26841,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____26852 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____26854 =
=======
                            (match uu____26874 with
                             | (uu____26886,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____26897 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____26899 =
>>>>>>> snap
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
<<<<<<< HEAD
                                     uu____26852 s uu____26854
                                    in
                                 let uu____26857 =
                                   let uu____26886 =
                                     let uu____26887 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____26887.FStar_Syntax_Syntax.n  in
                                   match uu____26886 with
=======
                                     uu____26897 s uu____26899
                                    in
                                 let uu____26902 =
                                   let uu____26931 =
                                     let uu____26932 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____26932.FStar_Syntax_Syntax.n  in
                                   match uu____26931 with
>>>>>>> snap
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
<<<<<<< HEAD
                                       let uu____26947 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____26947 with
                                        | (a::bs1,c3) ->
                                            let uu____27003 =
                                              let uu____27022 =
=======
                                       let uu____26992 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____26992 with
                                        | (a::bs1,c3) ->
                                            let uu____27048 =
                                              let uu____27067 =
>>>>>>> snap
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
<<<<<<< HEAD
                                                uu____27022
                                                (fun uu____27126  ->
                                                   match uu____27126 with
                                                   | (l1,l2) ->
                                                       let uu____27199 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____27199))
                                               in
                                            (match uu____27003 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____27304 ->
                                       let uu____27305 =
                                         let uu____27311 =
=======
                                                uu____27067
                                                (fun uu____27171  ->
                                                   match uu____27171 with
                                                   | (l1,l2) ->
                                                       let uu____27244 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____27244))
                                               in
                                            (match uu____27048 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____27349 ->
                                       let uu____27350 =
                                         let uu____27356 =
>>>>>>> snap
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
<<<<<<< HEAD
                                           uu____27311)
                                          in
                                       FStar_Errors.raise_error uu____27305 r
                                    in
                                 (match uu____26857 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____27387 =
                                        let uu____27394 =
                                          let uu____27395 =
                                            let uu____27396 =
                                              let uu____27403 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____27403,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____27396
                                             in
                                          [uu____27395]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____27394
                                          (fun b  ->
                                             let uu____27419 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____27421 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____27423 =
=======
                                           uu____27356)
                                          in
                                       FStar_Errors.raise_error uu____27350 r
                                    in
                                 (match uu____26902 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____27432 =
                                        let uu____27439 =
                                          let uu____27440 =
                                            let uu____27441 =
                                              let uu____27448 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____27448,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____27441
                                             in
                                          [uu____27440]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____27439
                                          (fun b  ->
                                             let uu____27464 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____27466 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____27468 =
>>>>>>> snap
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
<<<<<<< HEAD
                                               uu____27419 uu____27421
                                               uu____27423) r
                                         in
                                      (match uu____27387 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           let wl4 =
                                             let uu___3559_27433 = wl3  in
                                             {
                                               attempting =
                                                 (uu___3559_27433.attempting);
                                               wl_deferred =
                                                 (uu___3559_27433.wl_deferred);
                                               ctr = (uu___3559_27433.ctr);
                                               defer_ok =
                                                 (uu___3559_27433.defer_ok);
                                               smt_ok =
                                                 (uu___3559_27433.smt_ok);
                                               umax_heuristic_ok =
                                                 (uu___3559_27433.umax_heuristic_ok);
                                               tcenv =
                                                 (uu___3559_27433.tcenv);
=======
                                               uu____27464 uu____27466
                                               uu____27468) r
                                         in
                                      (match uu____27432 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           let wl4 =
                                             let uu___3563_27478 = wl3  in
                                             {
                                               attempting =
                                                 (uu___3563_27478.attempting);
                                               wl_deferred =
                                                 (uu___3563_27478.wl_deferred);
                                               ctr = (uu___3563_27478.ctr);
                                               defer_ok =
                                                 (uu___3563_27478.defer_ok);
                                               smt_ok =
                                                 (uu___3563_27478.smt_ok);
                                               umax_heuristic_ok =
                                                 (uu___3563_27478.umax_heuristic_ok);
                                               tcenv =
                                                 (uu___3563_27478.tcenv);
>>>>>>> snap
                                               wl_implicits =
                                                 (FStar_List.append
                                                    g_uvars.FStar_TypeChecker_Common.implicits
                                                    wl3.wl_implicits)
                                             }  in
                                           let substs =
                                             FStar_List.map2
                                               (fun b  ->
                                                  fun t  ->
<<<<<<< HEAD
                                                    let uu____27458 =
                                                      let uu____27465 =
=======
                                                    let uu____27503 =
                                                      let uu____27510 =
>>>>>>> snap
                                                        FStar_All.pipe_right
                                                          b
                                                          FStar_Pervasives_Native.fst
                                                         in
<<<<<<< HEAD
                                                      (uu____27465, t)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____27458) (a_b ::
=======
                                                      (uu____27510, t)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____27503) (a_b ::
>>>>>>> snap
                                               rest_bs)
                                               ((c21.FStar_Syntax_Syntax.result_typ)
                                               :: rest_bs_uvars)
                                              in
<<<<<<< HEAD
                                           let uu____27482 =
                                             let f_sort_is =
                                               let uu____27492 =
                                                 let uu____27493 =
                                                   let uu____27496 =
                                                     let uu____27497 =
=======
                                           let uu____27527 =
                                             let f_sort_is =
                                               let uu____27537 =
                                                 let uu____27538 =
                                                   let uu____27541 =
                                                     let uu____27542 =
>>>>>>> snap
                                                       FStar_All.pipe_right
                                                         f_b
                                                         FStar_Pervasives_Native.fst
                                                        in
<<<<<<< HEAD
                                                     uu____27497.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Subst.compress
                                                     uu____27496
                                                    in
                                                 uu____27493.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____27492 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____27508,uu____27509::is)
                                                   ->
                                                   let uu____27551 =
=======
                                                     uu____27542.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Subst.compress
                                                     uu____27541
                                                    in
                                                 uu____27538.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____27537 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____27553,uu____27554::is)
                                                   ->
                                                   let uu____27596 =
>>>>>>> snap
                                                     FStar_All.pipe_right is
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_All.pipe_right
<<<<<<< HEAD
                                                     uu____27551
                                                     (FStar_List.map
                                                        (FStar_Syntax_Subst.subst
                                                           substs))
                                               | uu____27584 ->
                                                   let uu____27585 =
                                                     let uu____27591 =
=======
                                                     uu____27596
                                                     (FStar_List.map
                                                        (FStar_Syntax_Subst.subst
                                                           substs))
                                               | uu____27629 ->
                                                   let uu____27630 =
                                                     let uu____27636 =
>>>>>>> snap
                                                       stronger_t_shape_error
                                                         "type of f is not a repr type"
                                                        in
                                                     (FStar_Errors.Fatal_UnexpectedExpressionType,
<<<<<<< HEAD
                                                       uu____27591)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____27585 r
                                                in
                                             let uu____27597 =
=======
                                                       uu____27636)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____27630 r
                                                in
                                             let uu____27642 =
>>>>>>> snap
                                               FStar_All.pipe_right
                                                 c12.FStar_Syntax_Syntax.effect_args
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_List.fold_left2
<<<<<<< HEAD
                                               (fun uu____27632  ->
                                                  fun f_sort_i  ->
                                                    fun c1_i  ->
                                                      match uu____27632 with
                                                      | (ps,wl5) ->
                                                          let uu____27653 =
=======
                                               (fun uu____27677  ->
                                                  fun f_sort_i  ->
                                                    fun c1_i  ->
                                                      match uu____27677 with
                                                      | (ps,wl5) ->
                                                          let uu____27698 =
>>>>>>> snap
                                                            sub_prob wl5
                                                              f_sort_i
                                                              FStar_TypeChecker_Common.EQ
                                                              c1_i
                                                              "indices of c1"
                                                             in
<<<<<<< HEAD
                                                          (match uu____27653
=======
                                                          (match uu____27698
>>>>>>> snap
                                                           with
                                                           | (p,wl6) ->
                                                               ((FStar_List.append
                                                                   ps 
                                                                   [p]), wl6)))
                                               ([], wl4) f_sort_is
<<<<<<< HEAD
                                               uu____27597
                                              in
                                           (match uu____27482 with
                                            | (f_sub_probs,wl5) ->
                                                let stronger_ct =
                                                  let uu____27678 =
=======
                                               uu____27642
                                              in
                                           (match uu____27527 with
                                            | (f_sub_probs,wl5) ->
                                                let stronger_ct =
                                                  let uu____27723 =
>>>>>>> snap
                                                    FStar_All.pipe_right
                                                      stronger_c
                                                      (FStar_Syntax_Subst.subst_comp
                                                         substs)
                                                     in
                                                  FStar_All.pipe_right
<<<<<<< HEAD
                                                    uu____27678
                                                    FStar_Syntax_Util.comp_to_comp_typ
                                                   in
                                                let uu____27679 =
                                                  let g_sort_is =
                                                    let uu____27689 =
                                                      let uu____27690 =
                                                        FStar_Syntax_Subst.compress
                                                          stronger_ct.FStar_Syntax_Syntax.result_typ
                                                         in
                                                      uu____27690.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____27689 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (uu____27695,uu____27696::is)
=======
                                                    uu____27723
                                                    FStar_Syntax_Util.comp_to_comp_typ
                                                   in
                                                let uu____27724 =
                                                  let g_sort_is =
                                                    let uu____27734 =
                                                      let uu____27735 =
                                                        FStar_Syntax_Subst.compress
                                                          stronger_ct.FStar_Syntax_Syntax.result_typ
                                                         in
                                                      uu____27735.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____27734 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (uu____27740,uu____27741::is)
>>>>>>> snap
                                                        ->
                                                        FStar_All.pipe_right
                                                          is
                                                          (FStar_List.map
                                                             FStar_Pervasives_Native.fst)
<<<<<<< HEAD
                                                    | uu____27764 ->
                                                        let uu____27765 =
                                                          let uu____27771 =
=======
                                                    | uu____27809 ->
                                                        let uu____27810 =
                                                          let uu____27816 =
>>>>>>> snap
                                                            stronger_t_shape_error
                                                              "return type is not a repr type"
                                                             in
                                                          (FStar_Errors.Fatal_UnexpectedExpressionType,
<<<<<<< HEAD
                                                            uu____27771)
                                                           in
                                                        FStar_Errors.raise_error
                                                          uu____27765 r
                                                     in
                                                  let uu____27777 =
=======
                                                            uu____27816)
                                                           in
                                                        FStar_Errors.raise_error
                                                          uu____27810 r
                                                     in
                                                  let uu____27822 =
>>>>>>> snap
                                                    FStar_All.pipe_right
                                                      c21.FStar_Syntax_Syntax.effect_args
                                                      (FStar_List.map
                                                         FStar_Pervasives_Native.fst)
                                                     in
                                                  FStar_List.fold_left2
<<<<<<< HEAD
                                                    (fun uu____27812  ->
                                                       fun g_sort_i  ->
                                                         fun c2_i  ->
                                                           match uu____27812
                                                           with
                                                           | (ps,wl6) ->
                                                               let uu____27833
=======
                                                    (fun uu____27857  ->
                                                       fun g_sort_i  ->
                                                         fun c2_i  ->
                                                           match uu____27857
                                                           with
                                                           | (ps,wl6) ->
                                                               let uu____27878
>>>>>>> snap
                                                                 =
                                                                 sub_prob wl6
                                                                   g_sort_i
                                                                   FStar_TypeChecker_Common.EQ
                                                                   c2_i
                                                                   "indices of c2"
                                                                  in
<<<<<<< HEAD
                                                               (match uu____27833
=======
                                                               (match uu____27878
>>>>>>> snap
                                                                with
                                                                | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                    ([], wl5) g_sort_is
<<<<<<< HEAD
                                                    uu____27777
                                                   in
                                                (match uu____27679 with
                                                 | (g_sub_probs,wl6) ->
                                                     let fml =
                                                       let uu____27860 =
                                                         let uu____27865 =
                                                           FStar_List.hd
                                                             stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                            in
                                                         let uu____27866 =
                                                           let uu____27867 =
=======
                                                    uu____27822
                                                   in
                                                (match uu____27724 with
                                                 | (g_sub_probs,wl6) ->
                                                     let fml =
                                                       let uu____27905 =
                                                         let uu____27910 =
                                                           FStar_List.hd
                                                             stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                            in
                                                         let uu____27911 =
                                                           let uu____27912 =
>>>>>>> snap
                                                             FStar_List.hd
                                                               stronger_ct.FStar_Syntax_Syntax.effect_args
                                                              in
                                                           FStar_Pervasives_Native.fst
<<<<<<< HEAD
                                                             uu____27867
                                                            in
                                                         (uu____27865,
                                                           uu____27866)
                                                          in
                                                       match uu____27860 with
                                                       | (u,wp) ->
                                                           let trivial_post =
                                                             let ts =
                                                               let uu____27894
=======
                                                             uu____27912
                                                            in
                                                         (uu____27910,
                                                           uu____27911)
                                                          in
                                                       match uu____27905 with
                                                       | (u,wp) ->
                                                           let trivial_post =
                                                             let ts =
                                                               let uu____27939
>>>>>>> snap
                                                                 =
                                                                 FStar_TypeChecker_Env.lookup_definition
                                                                   [FStar_TypeChecker_Env.NoDelta]
                                                                   env
                                                                   FStar_Parser_Const.trivial_pure_post_lid
                                                                  in
                                                               FStar_All.pipe_right
<<<<<<< HEAD
                                                                 uu____27894
                                                                 FStar_Util.must
                                                                in
                                                             let uu____27911
=======
                                                                 uu____27939
                                                                 FStar_Util.must
                                                                in
                                                             let uu____27956
>>>>>>> snap
                                                               =
                                                               FStar_TypeChecker_Env.inst_tscheme_with
                                                                 ts [u]
                                                                in
<<<<<<< HEAD
                                                             match uu____27911
                                                             with
                                                             | (uu____27916,t)
                                                                 ->
                                                                 let uu____27918
                                                                   =
                                                                   let uu____27923
                                                                    =
                                                                    let uu____27924
=======
                                                             match uu____27956
                                                             with
                                                             | (uu____27961,t)
                                                                 ->
                                                                 let uu____27963
                                                                   =
                                                                   let uu____27968
                                                                    =
                                                                    let uu____27969
>>>>>>> snap
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    stronger_ct.FStar_Syntax_Syntax.result_typ
                                                                    FStar_Syntax_Syntax.as_arg
                                                                     in
<<<<<<< HEAD
                                                                    [uu____27924]
                                                                     in
                                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                                    t
                                                                    uu____27923
                                                                    in
                                                                 uu____27918
                                                                   FStar_Pervasives_Native.None
                                                                   FStar_Range.dummyRange
                                                              in
                                                           let uu____27957 =
                                                             let uu____27962
                                                               =
                                                               let uu____27963
=======
                                                                    [uu____27969]
                                                                     in
                                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                                    t
                                                                    uu____27968
                                                                    in
                                                                 uu____27963
                                                                   FStar_Pervasives_Native.None
                                                                   FStar_Range.dummyRange
                                                              in
                                                           let uu____28002 =
                                                             let uu____28007
                                                               =
                                                               let uu____28008
>>>>>>> snap
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   trivial_post
                                                                   FStar_Syntax_Syntax.as_arg
                                                                  in
<<<<<<< HEAD
                                                               [uu____27963]
                                                                in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               wp uu____27962
                                                              in
                                                           uu____27957
=======
                                                               [uu____28008]
                                                                in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               wp uu____28007
                                                              in
                                                           uu____28002
>>>>>>> snap
                                                             FStar_Pervasives_Native.None
                                                             FStar_Range.dummyRange
                                                        in
                                                     let sub_probs =
<<<<<<< HEAD
                                                       let uu____27999 =
                                                         let uu____28002 =
                                                           let uu____28005 =
                                                             let uu____28008
=======
                                                       let uu____28044 =
                                                         let uu____28047 =
                                                           let uu____28050 =
                                                             let uu____28053
>>>>>>> snap
                                                               =
                                                               FStar_All.pipe_right
                                                                 g_lift.FStar_TypeChecker_Common.deferred
                                                                 (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                in
                                                             FStar_List.append
                                                               g_sub_probs
<<<<<<< HEAD
                                                               uu____28008
                                                              in
                                                           FStar_List.append
                                                             f_sub_probs
                                                             uu____28005
                                                            in
                                                         FStar_List.append
                                                           is_sub_probs
                                                           uu____28002
                                                          in
                                                       ret_sub_prob ::
                                                         uu____27999
                                                        in
                                                     let guard =
                                                       let guard =
                                                         let uu____28032 =
=======
                                                               uu____28053
                                                              in
                                                           FStar_List.append
                                                             f_sub_probs
                                                             uu____28050
                                                            in
                                                         FStar_List.append
                                                           is_sub_probs
                                                           uu____28047
                                                          in
                                                       ret_sub_prob ::
                                                         uu____28044
                                                        in
                                                     let guard =
                                                       let guard =
                                                         let uu____28077 =
>>>>>>> snap
                                                           FStar_List.map
                                                             p_guard
                                                             sub_probs
                                                            in
                                                         FStar_Syntax_Util.mk_conj_l
<<<<<<< HEAD
                                                           uu____28032
=======
                                                           uu____28077
>>>>>>> snap
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
<<<<<<< HEAD
                                                       let uu____28043 =
                                                         let uu____28046 =
=======
                                                       let uu____28088 =
                                                         let uu____28091 =
>>>>>>> snap
                                                           FStar_Syntax_Util.mk_conj
                                                             guard fml
                                                            in
                                                         FStar_All.pipe_left
<<<<<<< HEAD
                                                           (fun _28049  ->
                                                              FStar_Pervasives_Native.Some
                                                                _28049)
                                                           uu____28046
                                                          in
                                                       solve_prob orig
                                                         uu____28043 [] wl6
                                                        in
                                                     let uu____28050 =
                                                       attempt sub_probs wl7
                                                        in
                                                     solve env uu____28050)))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28073 =
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28075 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28075]
              | x -> x  in
            let c12 =
              let uu___3630_28078 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs1;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3630_28078.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3630_28078.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3630_28078.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3630_28078.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28079 =
              let uu____28084 =
                FStar_All.pipe_right
                  (let uu___3633_28086 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs1;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3633_28086.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3633_28086.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3633_28086.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3633_28086.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28084
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28079
              (fun uu____28100  ->
                 match uu____28100 with
                 | (c,g) ->
                     let uu____28107 =
                       let uu____28109 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28109  in
                     if uu____28107
                     then
                       let uu____28112 =
                         let uu____28118 =
                           let uu____28120 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28122 =
=======
                                                           (fun _28094  ->
                                                              FStar_Pervasives_Native.Some
                                                                _28094)
                                                           uu____28091
                                                          in
                                                       solve_prob orig
                                                         uu____28088 [] wl6
                                                        in
                                                     let uu____28095 =
                                                       attempt sub_probs wl7
                                                        in
                                                     solve env uu____28095)))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28118 =
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28120 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28120]
              | x -> x  in
            let c12 =
              let uu___3634_28123 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs1;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3634_28123.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3634_28123.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3634_28123.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3634_28123.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28124 =
              let uu____28129 =
                FStar_All.pipe_right
                  (let uu___3637_28131 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs1;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3637_28131.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3637_28131.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3637_28131.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3637_28131.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28129
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28124
              (fun uu____28145  ->
                 match uu____28145 with
                 | (c,g) ->
                     let uu____28152 =
                       let uu____28154 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28154  in
                     if uu____28152
                     then
                       let uu____28157 =
                         let uu____28163 =
                           let uu____28165 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28167 =
>>>>>>> snap
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
<<<<<<< HEAD
                             uu____28120 uu____28122
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28118)
                          in
                       FStar_Errors.raise_error uu____28112 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28128 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28128
=======
                             uu____28165 uu____28167
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28163)
                          in
                       FStar_Errors.raise_error uu____28157 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28173 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28173
>>>>>>> snap
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
<<<<<<< HEAD
              (let uu____28134 = lift_c1 ()  in
               solve_eq uu____28134 c21 FStar_TypeChecker_Env.trivial_guard)
=======
              (let uu____28179 = lift_c1 ()  in
               solve_eq uu____28179 c21 FStar_TypeChecker_Env.trivial_guard)
>>>>>>> snap
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
<<<<<<< HEAD
                      (fun uu___31_28143  ->
                         match uu___31_28143 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28148 -> false))
                  in
               let uu____28150 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28180)::uu____28181,(wp2,uu____28183)::uu____28184)
                     -> (wp1, wp2)
                 | uu____28257 ->
                     let uu____28282 =
                       let uu____28288 =
                         let uu____28290 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____28292 =
=======
                      (fun uu___31_28188  ->
                         match uu___31_28188 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28193 -> false))
                  in
               let uu____28195 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28225)::uu____28226,(wp2,uu____28228)::uu____28229)
                     -> (wp1, wp2)
                 | uu____28302 ->
                     let uu____28327 =
                       let uu____28333 =
                         let uu____28335 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____28337 =
>>>>>>> snap
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
<<<<<<< HEAD
                           uu____28290 uu____28292
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____28288)
                        in
                     FStar_Errors.raise_error uu____28282
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28150 with
               | (wpc1,wpc2) ->
                   let uu____28302 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____28302
                   then
                     let uu____28305 =
=======
                           uu____28335 uu____28337
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____28333)
                        in
                     FStar_Errors.raise_error uu____28327
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28195 with
               | (wpc1,wpc2) ->
                   let uu____28347 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____28347
                   then
                     let uu____28350 =
>>>>>>> snap
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
<<<<<<< HEAD
                     solve_t env uu____28305 wl
                   else
                     (let uu____28309 =
                        let uu____28316 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____28316  in
                      match uu____28309 with
                      | (c2_decl,qualifiers) ->
                          let uu____28337 =
=======
                     solve_t env uu____28350 wl
                   else
                     (let uu____28354 =
                        let uu____28361 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____28361  in
                      match uu____28354 with
                      | (c2_decl,qualifiers) ->
                          let uu____28382 =
>>>>>>> snap
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
<<<<<<< HEAD
                          if uu____28337
                          then
                            let c1_repr =
                              let uu____28344 =
                                let uu____28345 =
                                  let uu____28346 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____28346  in
                                let uu____28347 =
=======
                          if uu____28382
                          then
                            let c1_repr =
                              let uu____28389 =
                                let uu____28390 =
                                  let uu____28391 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____28391  in
                                let uu____28392 =
>>>>>>> snap
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
<<<<<<< HEAD
                                  uu____28345 uu____28347
=======
                                  uu____28390 uu____28392
>>>>>>> snap
                                 in
                              FStar_TypeChecker_Normalize.normalize
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
<<<<<<< HEAD
                                FStar_TypeChecker_Env.HNF] env uu____28344
                               in
                            let c2_repr =
                              let uu____28349 =
                                let uu____28350 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____28351 =
=======
                                FStar_TypeChecker_Env.HNF] env uu____28389
                               in
                            let c2_repr =
                              let uu____28394 =
                                let uu____28395 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____28396 =
>>>>>>> snap
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
<<<<<<< HEAD
                                  uu____28350 uu____28351
=======
                                  uu____28395 uu____28396
>>>>>>> snap
                                 in
                              FStar_TypeChecker_Normalize.normalize
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
<<<<<<< HEAD
                                FStar_TypeChecker_Env.HNF] env uu____28349
                               in
                            let uu____28352 =
                              let uu____28357 =
                                let uu____28359 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____28361 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____28359
                                  uu____28361
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____28357
                               in
                            (match uu____28352 with
=======
                                FStar_TypeChecker_Env.HNF] env uu____28394
                               in
                            let uu____28397 =
                              let uu____28402 =
                                let uu____28404 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____28406 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____28404
                                  uu____28406
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____28402
                               in
                            (match uu____28397 with
>>>>>>> snap
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
<<<<<<< HEAD
                                 let uu____28367 = attempt [prob] wl2  in
                                 solve env uu____28367)
=======
                                 let uu____28412 = attempt [prob] wl2  in
                                 solve env uu____28412)
>>>>>>> snap
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
=======
                  let uu____26283 =
                    FStar_Syntax_Print.args_to_string
                      c2_comp.FStar_Syntax_Syntax.effect_args
                     in
                  FStar_Util.format2
                    "incompatible effect arguments: %s <> %s" uu____26281
                    uu____26283
                   in
                giveup env uu____26279 orig)
             else
               (let uu____26288 =
                  sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                    FStar_TypeChecker_Common.EQ
                    c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                   in
                match uu____26288 with
                | (ret_sub_prob,wl1) ->
                    let uu____26296 =
                      FStar_List.fold_right2
                        (fun uu____26333  ->
                           fun uu____26334  ->
                             fun uu____26335  ->
                               match (uu____26333, uu____26334, uu____26335)
                               with
                               | ((a1,uu____26379),(a2,uu____26381),(arg_sub_probs,wl2))
                                   ->
                                   let uu____26414 =
                                     sub_prob wl2 a1
                                       FStar_TypeChecker_Common.EQ a2
                                       "effect arg"
                                      in
                                   (match uu____26414 with
                                    | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                        c1_comp.FStar_Syntax_Syntax.effect_args
                        c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                       in
                    (match uu____26296 with
                     | (arg_sub_probs,wl2) ->
                         let sub_probs = ret_sub_prob :: arg_sub_probs  in
                         let guard =
                           let uu____26444 = FStar_List.map p_guard sub_probs
                              in
                           FStar_Syntax_Util.mk_conj_l uu____26444  in
                         let wl3 =
                           solve_prob orig
                             (FStar_Pervasives_Native.Some guard) [] wl2
                            in
                         let uu____26452 = attempt sub_probs wl3  in
                         solve env uu____26452)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____26475 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____26478)::[] -> wp1
              | uu____26503 ->
                  let uu____26514 =
                    let uu____26516 =
                      let uu____26518 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____26518  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____26516
                     in
                  failwith uu____26514
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____26525 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____26525]
              | x -> x  in
            let uu____26527 =
              let uu____26538 =
                let uu____26547 =
                  let uu____26548 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____26548 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____26547  in
              [uu____26538]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____26527;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____26566 = lift_c1 ()  in solve_eq uu____26566 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___31_26575  ->
                       match uu___31_26575 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____26580 -> false))
                in
             let uu____26582 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____26612)::uu____26613,(wp2,uu____26615)::uu____26616)
                   -> (wp1, wp2)
               | uu____26689 ->
                   let uu____26714 =
                     let uu____26720 =
                       let uu____26722 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____26724 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____26722 uu____26724
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____26720)
                      in
                   FStar_Errors.raise_error uu____26714
                     env.FStar_TypeChecker_Env.range
                in
             match uu____26582 with
             | (wpc1,wpc2) ->
                 let uu____26734 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____26734
                 then
                   let uu____26739 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____26739 wl
                 else
                   (let uu____26743 =
                      let uu____26750 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____26750  in
                    match uu____26743 with
                    | (c2_decl,qualifiers) ->
                        let uu____26771 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____26771
                        then
                          let c1_repr =
                            let uu____26778 =
                              let uu____26779 =
                                let uu____26780 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____26780  in
                              let uu____26781 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____26779 uu____26781
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____26778
                             in
                          let c2_repr =
                            let uu____26783 =
                              let uu____26784 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____26785 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____26784 uu____26785
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____26783
                             in
                          let uu____26786 =
                            let uu____26791 =
                              let uu____26793 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____26795 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____26793 uu____26795
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____26791
                             in
                          (match uu____26786 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____26801 = attempt [prob] wl2  in
                               solve env uu____26801)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____26816 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____26816
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____26825 =
                                     let uu____26832 =
                                       let uu____26833 =
                                         let uu____26850 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____26853 =
                                           let uu____26864 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____26873 =
                                             let uu____26884 =
                                               let uu____26893 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____26893
                                                in
                                             [uu____26884]  in
                                           uu____26864 :: uu____26873  in
                                         (uu____26850, uu____26853)  in
                                       FStar_Syntax_Syntax.Tm_app uu____26833
                                        in
                                     FStar_Syntax_Syntax.mk uu____26832  in
                                   uu____26825 FStar_Pervasives_Native.None r))
>>>>>>> snap
                               else
                                 (let wpc1_2 =
<<<<<<< HEAD
                                    let uu____28387 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____28387
=======
                                    let uu____28432 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____28432
>>>>>>> snap
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
<<<<<<< HEAD
                                  if is_null_wp_2
                                  then
<<<<<<< HEAD
                                    ((let uu____28410 =
=======
                                    ((let uu____28455 =
>>>>>>> snap
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
<<<<<<< HEAD
                                      if uu____28410
=======
                                      if uu____28455
>>>>>>> snap
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
                                        match c2_decl.FStar_Syntax_Syntax.trivial
                                        with
                                        | FStar_Pervasives_Native.None  ->
                                            failwith
                                              "Rel doesn't yet handle undefined trivial combinator in an effect"
                                        | FStar_Pervasives_Native.Some t -> t
                                         in
<<<<<<< HEAD
                                      let uu____28422 =
                                        let uu____28429 =
                                          let uu____28430 =
                                            let uu____28447 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____28450 =
                                              let uu____28461 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____28461; wpc1_2]  in
                                            (uu____28447, uu____28450)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____28430
                                           in
                                        FStar_Syntax_Syntax.mk uu____28429
                                         in
                                      uu____28422
=======
                                      let uu____28467 =
                                        let uu____28474 =
                                          let uu____28475 =
                                            let uu____28492 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____28495 =
                                              let uu____28506 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____28506; wpc1_2]  in
                                            (uu____28492, uu____28495)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____28475
                                           in
                                        FStar_Syntax_Syntax.mk uu____28474
                                         in
                                      uu____28467
>>>>>>> snap
                                        FStar_Pervasives_Native.None r))
                                  else
                                    (let c2_univ =
                                       env.FStar_TypeChecker_Env.universe_of
                                         env
                                         c21.FStar_Syntax_Syntax.result_typ
                                        in
<<<<<<< HEAD
                                     let uu____28509 =
                                       let uu____28516 =
                                         let uu____28517 =
                                           let uu____28534 =
=======
                                     let uu____28554 =
                                       let uu____28561 =
                                         let uu____28562 =
                                           let uu____28579 =
>>>>>>> snap
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl
                                               c2_decl.FStar_Syntax_Syntax.stronger
                                              in
<<<<<<< HEAD
                                           let uu____28537 =
                                             let uu____28548 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____28557 =
                                               let uu____28568 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____28568; wpc1_2]  in
                                             uu____28548 :: uu____28557  in
                                           (uu____28534, uu____28537)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____28517
                                          in
                                       FStar_Syntax_Syntax.mk uu____28516  in
                                     uu____28509 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____28622 =
=======
                                           let uu____28582 =
                                             let uu____28593 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____28602 =
                                               let uu____28613 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____28613; wpc1_2]  in
                                             uu____28593 :: uu____28602  in
                                           (uu____28579, uu____28582)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____28562
                                          in
                                       FStar_Syntax_Syntax.mk uu____28561  in
                                     uu____28554 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____28667 =
>>>>>>> snap
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
<<<<<<< HEAD
                              if uu____28622
                              then
                                let uu____28627 =
                                  let uu____28629 =
=======
                              if uu____28667
                              then
                                let uu____28672 =
                                  let uu____28674 =
>>>>>>> snap
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
<<<<<<< HEAD
                                    uu____28629
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____28627
                              else ());
                             (let uu____28633 =
=======
                                    uu____28674
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____28672
                              else ());
                             (let uu____28678 =
>>>>>>> snap
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
<<<<<<< HEAD
                              match uu____28633 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____28642 =
                                      let uu____28645 =
=======
                              match uu____28678 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____28687 =
                                      let uu____28690 =
>>>>>>> snap
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
<<<<<<< HEAD
                                        (fun _28648  ->
                                           FStar_Pervasives_Native.Some
                                             _28648) uu____28645
                                       in
                                    solve_prob orig uu____28642 [] wl1  in
                                  let uu____28649 = attempt [base_prob] wl2
                                     in
                                  solve env uu____28649))))
           in
        let uu____28650 = FStar_Util.physical_equality c1 c2  in
        if uu____28650
        then
          let uu____28653 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____28653
        else
          ((let uu____28657 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____28657
            then
              let uu____28662 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____28664 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____28662
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____28664
            else ());
           (let uu____28669 =
              let uu____28678 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____28681 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____28678, uu____28681)  in
            match uu____28669 with
=======
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____26942 =
                                    let uu____26949 =
                                      let uu____26950 =
                                        let uu____26967 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____26970 =
                                          let uu____26981 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____26990 =
                                            let uu____27001 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____27010 =
                                              let uu____27021 =
                                                let uu____27030 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____27030
                                                 in
                                              [uu____27021]  in
                                            uu____27001 :: uu____27010  in
                                          uu____26981 :: uu____26990  in
                                        (uu____26967, uu____26970)  in
                                      FStar_Syntax_Syntax.Tm_app uu____26950
                                       in
                                    FStar_Syntax_Syntax.mk uu____26949  in
                                  uu____26942 FStar_Pervasives_Native.None r)
                              in
                           (let uu____27084 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____27084
                            then
                              let uu____27089 =
                                let uu____27091 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____27091
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____27089
                            else ());
                           (let uu____27095 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____27095 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____27104 =
                                    let uu____27107 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _27110  ->
                                         FStar_Pervasives_Native.Some _27110)
                                      uu____27107
                                     in
                                  solve_prob orig uu____27104 [] wl1  in
                                let uu____27111 = attempt [base_prob] wl2  in
                                solve env uu____27111))))
           in
        let uu____27112 = FStar_Util.physical_equality c1 c2  in
        if uu____27112
        then
          let uu____27115 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____27115
        else
          ((let uu____27119 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____27119
            then
              let uu____27124 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____27126 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____27124
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____27126
            else ());
           (let uu____27131 =
              let uu____27140 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____27143 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____27140, uu____27143)  in
            match uu____27131 with
>>>>>>> snap
=======
                                        (fun _28693  ->
                                           FStar_Pervasives_Native.Some
                                             _28693) uu____28690
                                       in
                                    solve_prob orig uu____28687 [] wl1  in
                                  let uu____28694 = attempt [base_prob] wl2
                                     in
                                  solve env uu____28694))))
           in
        let uu____28695 = FStar_Util.physical_equality c1 c2  in
        if uu____28695
        then
          let uu____28698 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____28698
        else
          ((let uu____28702 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____28702
            then
              let uu____28707 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____28709 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____28707
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____28709
            else ());
           (let uu____28714 =
              let uu____28723 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____28726 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____28723, uu____28726)  in
            match uu____28714 with
>>>>>>> snap
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
<<<<<<< HEAD
<<<<<<< HEAD
                    (t1,uu____28699),FStar_Syntax_Syntax.Total
                    (t2,uu____28701)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____28718 =
=======
                    (t1,uu____27161),FStar_Syntax_Syntax.Total
                    (t2,uu____27163)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____27180 =
>>>>>>> snap
=======
                    (t1,uu____28744),FStar_Syntax_Syntax.Total
                    (t2,uu____28746)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____28763 =
>>>>>>> snap
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
<<<<<<< HEAD
<<<<<<< HEAD
                     solve_t env uu____28718 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____28720,FStar_Syntax_Syntax.Total uu____28721) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____28740),FStar_Syntax_Syntax.Total
                    (t2,uu____28742)) ->
                     let uu____28759 =
=======
                     solve_t env uu____27180 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____27182,FStar_Syntax_Syntax.Total uu____27183) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____27202),FStar_Syntax_Syntax.Total
                    (t2,uu____27204)) ->
                     let uu____27221 =
>>>>>>> snap
=======
                     solve_t env uu____28763 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____28765,FStar_Syntax_Syntax.Total uu____28766) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____28785),FStar_Syntax_Syntax.Total
                    (t2,uu____28787)) ->
                     let uu____28804 =
>>>>>>> snap
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
<<<<<<< HEAD
<<<<<<< HEAD
                     solve_t env uu____28759 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____28762),FStar_Syntax_Syntax.GTotal
                    (t2,uu____28764)) ->
                     let uu____28781 =
=======
                     solve_t env uu____27221 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____27224),FStar_Syntax_Syntax.GTotal
                    (t2,uu____27226)) ->
                     let uu____27243 =
>>>>>>> snap
=======
                     solve_t env uu____28804 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____28807),FStar_Syntax_Syntax.GTotal
                    (t2,uu____28809)) ->
                     let uu____28826 =
>>>>>>> snap
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
<<<<<<< HEAD
<<<<<<< HEAD
                     solve_t env uu____28781 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____28784),FStar_Syntax_Syntax.GTotal
                    (t2,uu____28786)) ->
=======
                     solve_t env uu____27243 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____27246),FStar_Syntax_Syntax.GTotal
                    (t2,uu____27248)) ->
>>>>>>> snap
=======
                     solve_t env uu____28826 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____28829),FStar_Syntax_Syntax.GTotal
                    (t2,uu____28831)) ->
>>>>>>> snap
                     if
                       problem.FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.SUB
                     then
<<<<<<< HEAD
<<<<<<< HEAD
                       let uu____28804 =
=======
                       let uu____27266 =
>>>>>>> snap
=======
                       let uu____28849 =
>>>>>>> snap
                         problem_using_guard orig t1
                           problem.FStar_TypeChecker_Common.relation t2
                           FStar_Pervasives_Native.None "result type"
                          in
<<<<<<< HEAD
<<<<<<< HEAD
                       solve_t env uu____28804 wl
                     else giveup env "GTot =/= Tot" orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____28809,FStar_Syntax_Syntax.Comp uu____28810) ->
                     let uu____28819 =
                       let uu___3748_28822 = problem  in
                       let uu____28825 =
                         let uu____28826 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____28826
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3748_28822.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____28825;
                         FStar_TypeChecker_Common.relation =
                           (uu___3748_28822.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3748_28822.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3748_28822.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3748_28822.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3748_28822.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3748_28822.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3748_28822.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3748_28822.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____28819 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____28827,FStar_Syntax_Syntax.Comp uu____28828) ->
                     let uu____28837 =
                       let uu___3748_28840 = problem  in
                       let uu____28843 =
                         let uu____28844 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____28844
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3748_28840.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____28843;
                         FStar_TypeChecker_Common.relation =
                           (uu___3748_28840.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3748_28840.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3748_28840.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3748_28840.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3748_28840.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3748_28840.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3748_28840.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3748_28840.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____28837 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____28845,FStar_Syntax_Syntax.GTotal uu____28846) ->
                     let uu____28855 =
                       let uu___3760_28858 = problem  in
                       let uu____28861 =
                         let uu____28862 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____28862
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3760_28858.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3760_28858.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3760_28858.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____28861;
                         FStar_TypeChecker_Common.element =
                           (uu___3760_28858.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3760_28858.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3760_28858.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3760_28858.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3760_28858.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3760_28858.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____28855 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____28863,FStar_Syntax_Syntax.Total uu____28864) ->
                     let uu____28873 =
                       let uu___3760_28876 = problem  in
                       let uu____28879 =
                         let uu____28880 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____28880
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3760_28876.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3760_28876.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3760_28876.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____28879;
                         FStar_TypeChecker_Common.element =
                           (uu___3760_28876.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3760_28876.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3760_28876.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3760_28876.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3760_28876.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3760_28876.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____28873 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____28881,FStar_Syntax_Syntax.Comp uu____28882) ->
                     let uu____28883 =
=======
                       solve_t env uu____27266 wl
                     else giveup env "GTot =/= Tot" orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____27271,FStar_Syntax_Syntax.Comp uu____27272) ->
                     let uu____27281 =
                       let uu___3577_27284 = problem  in
                       let uu____27287 =
                         let uu____27288 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27288
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3577_27284.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____27287;
                         FStar_TypeChecker_Common.relation =
                           (uu___3577_27284.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3577_27284.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3577_27284.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3577_27284.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3577_27284.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3577_27284.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3577_27284.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3577_27284.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____27281 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____27289,FStar_Syntax_Syntax.Comp uu____27290) ->
                     let uu____27299 =
                       let uu___3577_27302 = problem  in
                       let uu____27305 =
                         let uu____27306 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27306
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3577_27302.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____27305;
                         FStar_TypeChecker_Common.relation =
                           (uu___3577_27302.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3577_27302.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3577_27302.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3577_27302.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3577_27302.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3577_27302.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3577_27302.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3577_27302.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____27299 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____27307,FStar_Syntax_Syntax.GTotal uu____27308) ->
                     let uu____27317 =
                       let uu___3589_27320 = problem  in
                       let uu____27323 =
                         let uu____27324 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27324
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3589_27320.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3589_27320.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3589_27320.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____27323;
                         FStar_TypeChecker_Common.element =
                           (uu___3589_27320.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3589_27320.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3589_27320.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3589_27320.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3589_27320.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3589_27320.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____27317 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____27325,FStar_Syntax_Syntax.Total uu____27326) ->
                     let uu____27335 =
                       let uu___3589_27338 = problem  in
                       let uu____27341 =
                         let uu____27342 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27342
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3589_27338.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3589_27338.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3589_27338.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____27341;
                         FStar_TypeChecker_Common.element =
                           (uu___3589_27338.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3589_27338.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3589_27338.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3589_27338.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3589_27338.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3589_27338.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____27335 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____27343,FStar_Syntax_Syntax.Comp uu____27344) ->
                     let uu____27345 =
>>>>>>> snap
=======
                       solve_t env uu____28849 wl
                     else giveup env "GTot =/= Tot" orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____28854,FStar_Syntax_Syntax.Comp uu____28855) ->
                     let uu____28864 =
                       let uu___3752_28867 = problem  in
                       let uu____28870 =
                         let uu____28871 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____28871
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3752_28867.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____28870;
                         FStar_TypeChecker_Common.relation =
                           (uu___3752_28867.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3752_28867.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3752_28867.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3752_28867.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3752_28867.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3752_28867.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3752_28867.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3752_28867.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____28864 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____28872,FStar_Syntax_Syntax.Comp uu____28873) ->
                     let uu____28882 =
                       let uu___3752_28885 = problem  in
                       let uu____28888 =
                         let uu____28889 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____28889
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3752_28885.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____28888;
                         FStar_TypeChecker_Common.relation =
                           (uu___3752_28885.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3752_28885.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3752_28885.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3752_28885.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3752_28885.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3752_28885.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3752_28885.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3752_28885.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____28882 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____28890,FStar_Syntax_Syntax.GTotal uu____28891) ->
                     let uu____28900 =
                       let uu___3764_28903 = problem  in
                       let uu____28906 =
                         let uu____28907 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____28907
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3764_28903.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3764_28903.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3764_28903.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____28906;
                         FStar_TypeChecker_Common.element =
                           (uu___3764_28903.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3764_28903.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3764_28903.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3764_28903.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3764_28903.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3764_28903.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____28900 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____28908,FStar_Syntax_Syntax.Total uu____28909) ->
                     let uu____28918 =
                       let uu___3764_28921 = problem  in
                       let uu____28924 =
                         let uu____28925 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____28925
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3764_28921.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3764_28921.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3764_28921.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____28924;
                         FStar_TypeChecker_Common.element =
                           (uu___3764_28921.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3764_28921.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3764_28921.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3764_28921.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3764_28921.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3764_28921.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____28918 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____28926,FStar_Syntax_Syntax.Comp uu____28927) ->
                     let uu____28928 =
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
                     if uu____28883
                     then
                       let uu____28886 =
=======
                     if uu____27345
                     then
                       let uu____27348 =
>>>>>>> snap
=======
                     if uu____28928
                     then
                       let uu____28931 =
>>>>>>> snap
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
<<<<<<< HEAD
<<<<<<< HEAD
                       solve_t env uu____28886 wl
=======
                       solve_t env uu____27348 wl
>>>>>>> snap
=======
                       solve_t env uu____28931 wl
>>>>>>> snap
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
<<<<<<< HEAD
<<<<<<< HEAD
                          let uu____28893 =
                            let uu____28898 =
=======
                          let uu____27355 =
                            let uu____27360 =
>>>>>>> snap
=======
                          let uu____28938 =
                            let uu____28943 =
>>>>>>> snap
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
<<<<<<< HEAD
<<<<<<< HEAD
                            if uu____28898
                            then (c1_comp, c2_comp)
                            else
                              (let uu____28907 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____28908 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____28907, uu____28908))
                             in
                          match uu____28893 with
=======
                            if uu____28943
                            then (c1_comp, c2_comp)
                            else
                              (let uu____28952 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____28953 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____28952, uu____28953))
                             in
                          match uu____28938 with
>>>>>>> snap
                          | (c1_comp1,c2_comp1) ->
                              solve_eq c1_comp1 c2_comp1
                                FStar_TypeChecker_Env.trivial_guard
=======
                            if uu____27360
                            then (c1_comp, c2_comp)
                            else
                              (let uu____27369 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____27370 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____27369, uu____27370))
                             in
                          match uu____27355 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
>>>>>>> snap
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11
                              in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21
                              in
<<<<<<< HEAD
<<<<<<< HEAD
                           (let uu____28916 =
=======
                           (let uu____27378 =
>>>>>>> snap
=======
                           (let uu____28961 =
>>>>>>> snap
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
<<<<<<< HEAD
<<<<<<< HEAD
                            if uu____28916
=======
                            if uu____27378
>>>>>>> snap
=======
                            if uu____28961
>>>>>>> snap
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
<<<<<<< HEAD
<<<<<<< HEAD
                           (let uu____28924 =
=======
                           (let uu____27386 =
>>>>>>> snap
=======
                           (let uu____28969 =
>>>>>>> snap
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
<<<<<<< HEAD
<<<<<<< HEAD
                            match uu____28924 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____28927 =
                                  let uu____28929 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____28931 =
=======
                            match uu____27386 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____27389 =
                                  let uu____27391 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____27393 =
>>>>>>> snap
=======
                            match uu____28969 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____28972 =
                                  let uu____28974 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____28976 =
>>>>>>> snap
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
<<<<<<< HEAD
<<<<<<< HEAD
                                    uu____28929 uu____28931
                                   in
                                giveup env uu____28927 orig
=======
                                    uu____27391 uu____27393
                                   in
                                giveup env uu____27389 orig
>>>>>>> snap
=======
                                    uu____28974 uu____28976
                                   in
                                giveup env uu____28972 orig
>>>>>>> snap
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____28942 =
=======
    let uu____28987 =
>>>>>>> snap
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
=======
    let uu____27404 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
>>>>>>> snap
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
<<<<<<< HEAD
<<<<<<< HEAD
    FStar_All.pipe_right uu____28942 (FStar_String.concat ", ")
=======
    FStar_All.pipe_right uu____27404 (FStar_String.concat ", ")
>>>>>>> snap
=======
    FStar_All.pipe_right uu____28987 (FStar_String.concat ", ")
>>>>>>> snap
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____28992 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____28992 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29017 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29048  ->
                match uu____29048 with
                | (u1,u2) ->
                    let uu____29056 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29058 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29056 uu____29058))
         in
      FStar_All.pipe_right uu____29017 (FStar_String.concat ", ")  in
=======
      let uu____27454 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____27454 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____27479 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____27510  ->
                match uu____27510 with
                | (u1,u2) ->
                    let uu____27518 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____27520 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____27518 uu____27520))
         in
      FStar_All.pipe_right uu____27479 (FStar_String.concat ", ")  in
>>>>>>> snap
=======
      let uu____29037 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29037 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29062 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29093  ->
                match uu____29093 with
                | (u1,u2) ->
                    let uu____29101 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29103 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29101 uu____29103))
         in
      FStar_All.pipe_right uu____29062 (FStar_String.concat ", ")  in
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29095,[])) when
          let uu____29122 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29122 -> "{}"
      | uu____29125 ->
=======
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____27557,[])) when
          let uu____27584 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____27584 -> "{}"
      | uu____27587 ->
>>>>>>> snap
=======
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29140,[])) when
          let uu____29167 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29167 -> "{}"
      | uu____29170 ->
>>>>>>> snap
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
<<<<<<< HEAD
<<<<<<< HEAD
                let uu____29152 =
=======
                let uu____27614 =
>>>>>>> snap
=======
                let uu____29197 =
>>>>>>> snap
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
<<<<<<< HEAD
<<<<<<< HEAD
                if uu____29152
=======
                if uu____27614
>>>>>>> snap
=======
                if uu____29197
>>>>>>> snap
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
<<<<<<< HEAD
<<<<<<< HEAD
            let uu____29164 =
              FStar_List.map
                (fun uu____29177  ->
                   match uu____29177 with
                   | (uu____29184,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Common.deferred
               in
            FStar_All.pipe_right uu____29164 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____29195 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____29195 imps
=======
            let uu____27626 =
              FStar_List.map
                (fun uu____27639  ->
                   match uu____27639 with
                   | (uu____27646,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____27626 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____27657 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____27657 imps
>>>>>>> snap
=======
            let uu____29209 =
              FStar_List.map
                (fun uu____29222  ->
                   match uu____29222 with
                   | (uu____29229,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Common.deferred
               in
            FStar_All.pipe_right uu____29209 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____29240 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____29240 imps
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
                  let uu____29252 =
=======
                  let uu____27714 =
>>>>>>> snap
=======
                  let uu____29297 =
>>>>>>> snap
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
<<<<<<< HEAD
<<<<<<< HEAD
                  if uu____29252
                  then
                    let uu____29260 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____29262 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____29260
                      (rel_to_string rel) uu____29262
                  else "TOP"  in
                let uu____29268 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____29268 with
=======
                  if uu____27714
                  then
                    let uu____27722 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____27724 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____27722
                      (rel_to_string rel) uu____27724
                  else "TOP"  in
                let uu____27730 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____27730 with
>>>>>>> snap
=======
                  if uu____29297
                  then
                    let uu____29305 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____29307 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____29305
                      (rel_to_string rel) uu____29307
                  else "TOP"  in
                let uu____29313 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____29313 with
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
              let uu____29328 =
                let uu____29331 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _29334  -> FStar_Pervasives_Native.Some _29334)
                  uu____29331
                 in
              FStar_Syntax_Syntax.new_bv uu____29328 t1  in
            let uu____29335 =
              let uu____29340 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____29340
               in
            match uu____29335 with | (p,wl1) -> (p, x, wl1)
=======
              let uu____27790 =
                let uu____27793 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _27796  -> FStar_Pervasives_Native.Some _27796)
                  uu____27793
                 in
              FStar_Syntax_Syntax.new_bv uu____27790 t1  in
            let uu____27797 =
              let uu____27802 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____27802
               in
            match uu____27797 with | (p,wl1) -> (p, x, wl1)
>>>>>>> snap
=======
              let uu____29373 =
                let uu____29376 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _29379  -> FStar_Pervasives_Native.Some _29379)
                  uu____29376
                 in
              FStar_Syntax_Syntax.new_bv uu____29373 t1  in
            let uu____29380 =
              let uu____29385 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____29385
               in
            match uu____29380 with | (p,wl1) -> (p, x, wl1)
>>>>>>> snap
  
let (solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob * Prims.string) ->
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
<<<<<<< HEAD
<<<<<<< HEAD
        (let uu____29400 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____29400
         then
           let uu____29405 =
=======
        (let uu____27862 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____27862
         then
           let uu____27867 =
>>>>>>> snap
=======
        (let uu____29445 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____29445
         then
           let uu____29450 =
>>>>>>> snap
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
<<<<<<< HEAD
<<<<<<< HEAD
           FStar_Util.print1 "solving problems %s {\n" uu____29405
         else ());
        (let uu____29412 =
           FStar_Util.record_time (fun uu____29419  -> solve env probs)  in
         match uu____29412 with
         | (sol,ms) ->
             ((let uu____29431 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____29431
               then
                 let uu____29436 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____29436
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____29449 =
                     FStar_Util.record_time
                       (fun uu____29456  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____29449 with
                    | ((),ms1) ->
                        ((let uu____29467 =
=======
           FStar_Util.print1 "solving problems %s {\n" uu____27867
         else ());
        (let uu____27874 =
           FStar_Util.record_time (fun uu____27881  -> solve env probs)  in
         match uu____27874 with
         | (sol,ms) ->
             ((let uu____27893 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____27893
               then
                 let uu____27898 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____27898
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____27911 =
                     FStar_Util.record_time
                       (fun uu____27918  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____27911 with
                    | ((),ms1) ->
                        ((let uu____27929 =
>>>>>>> snap
=======
           FStar_Util.print1 "solving problems %s {\n" uu____29450
         else ());
        (let uu____29457 =
           FStar_Util.record_time (fun uu____29464  -> solve env probs)  in
         match uu____29457 with
         | (sol,ms) ->
             ((let uu____29476 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____29476
               then
                 let uu____29481 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____29481
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____29494 =
                     FStar_Util.record_time
                       (fun uu____29501  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____29494 with
                    | ((),ms1) ->
                        ((let uu____29512 =
>>>>>>> snap
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
<<<<<<< HEAD
<<<<<<< HEAD
                          if uu____29467
                          then
                            let uu____29472 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____29472
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____29486 =
=======
                          if uu____27929
                          then
                            let uu____27934 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____27934
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____27948 =
>>>>>>> snap
=======
                          if uu____29512
                          then
                            let uu____29517 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____29517
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____29531 =
>>>>>>> snap
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
<<<<<<< HEAD
<<<<<<< HEAD
                     if uu____29486
                     then
                       let uu____29493 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____29493
=======
                     if uu____27948
                     then
                       let uu____27955 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____27955
>>>>>>> snap
=======
                     if uu____29531
                     then
                       let uu____29538 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____29538
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
          ((let uu____29520 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____29520
            then
              let uu____29525 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____29525
=======
          ((let uu____27982 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____27982
            then
              let uu____27987 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____27987
>>>>>>> snap
=======
          ((let uu____29565 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____29565
            then
              let uu____29570 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____29570
>>>>>>> snap
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
<<<<<<< HEAD
<<<<<<< HEAD
            (let uu____29532 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____29532
             then
               let uu____29537 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____29537
             else ());
            (let f2 =
               let uu____29543 =
                 let uu____29544 = FStar_Syntax_Util.unmeta f1  in
                 uu____29544.FStar_Syntax_Syntax.n  in
               match uu____29543 with
=======
            (let uu____27994 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____27994
             then
               let uu____27999 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____27999
             else ());
            (let f2 =
               let uu____28005 =
                 let uu____28006 = FStar_Syntax_Util.unmeta f1  in
                 uu____28006.FStar_Syntax_Syntax.n  in
               match uu____28005 with
>>>>>>> snap
=======
            (let uu____29577 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____29577
             then
               let uu____29582 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____29582
             else ());
            (let f2 =
               let uu____29588 =
                 let uu____29589 = FStar_Syntax_Util.unmeta f1  in
                 uu____29589.FStar_Syntax_Syntax.n  in
               match uu____29588 with
>>>>>>> snap
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
<<<<<<< HEAD
<<<<<<< HEAD
               | uu____29548 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3876_29549 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred =
                 (uu___3876_29549.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___3876_29549.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___3876_29549.FStar_TypeChecker_Common.implicits)
=======
               | uu____28010 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3705_28011 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___3705_28011.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___3705_28011.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___3705_28011.FStar_TypeChecker_Env.implicits)
>>>>>>> snap
=======
               | uu____29593 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3880_29594 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred =
                 (uu___3880_29594.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___3880_29594.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___3880_29594.FStar_TypeChecker_Common.implicits)
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
            let uu____29592 =
              let uu____29593 =
                let uu____29594 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _29595  ->
                       FStar_TypeChecker_Common.NonTrivial _29595)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____29594;
=======
            let uu____29637 =
              let uu____29638 =
                let uu____29639 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _29640  ->
                       FStar_TypeChecker_Common.NonTrivial _29640)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____29639;
>>>>>>> snap
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
<<<<<<< HEAD
              simplify_guard env uu____29593  in
            FStar_All.pipe_left
              (fun _29602  -> FStar_Pervasives_Native.Some _29602)
              uu____29592
  
let with_guard_no_simp :
  'Auu____29612 .
    'Auu____29612 ->
=======
            let uu____28066 =
              let uu____28067 =
                let uu____28068 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _28069  ->
                       FStar_TypeChecker_Common.NonTrivial _28069)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____28068;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____28067  in
            FStar_All.pipe_left
              (fun _28076  -> FStar_Pervasives_Native.Some _28076)
              uu____28066
  
let with_guard_no_simp :
  'Auu____28086 .
    'Auu____28086 ->
>>>>>>> snap
=======
              simplify_guard env uu____29638  in
            FStar_All.pipe_left
              (fun _29647  -> FStar_Pervasives_Native.Some _29647)
              uu____29637
  
let with_guard_no_simp :
  'Auu____29657 .
    'Auu____29657 ->
>>>>>>> snap
      FStar_TypeChecker_Common.prob ->
        FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option ->
          FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some d ->
<<<<<<< HEAD
<<<<<<< HEAD
            let uu____29635 =
              let uu____29636 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _29637  -> FStar_TypeChecker_Common.NonTrivial _29637)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____29636;
=======
            let uu____29680 =
              let uu____29681 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _29682  -> FStar_TypeChecker_Common.NonTrivial _29682)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____29681;
>>>>>>> snap
                FStar_TypeChecker_Common.deferred = d;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = []
              }  in
<<<<<<< HEAD
            FStar_Pervasives_Native.Some uu____29635
=======
            let uu____28109 =
              let uu____28110 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _28111  -> FStar_TypeChecker_Common.NonTrivial _28111)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____28110;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____28109
>>>>>>> snap
=======
            FStar_Pervasives_Native.Some uu____29680
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
          (let uu____29670 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____29670
           then
             let uu____29675 = FStar_Syntax_Print.term_to_string t1  in
             let uu____29677 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____29675
               uu____29677
           else ());
          (let uu____29682 =
             let uu____29687 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____29687
              in
           match uu____29682 with
           | (prob,wl) ->
               let g =
                 let uu____29695 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____29703  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____29695  in
               ((let uu____29722 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____29722
                 then
                   let uu____29727 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____29727
=======
          (let uu____28144 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____28144
           then
             let uu____28149 = FStar_Syntax_Print.term_to_string t1  in
             let uu____28151 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____28149
               uu____28151
           else ());
          (let uu____28156 =
             let uu____28161 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____28161
              in
           match uu____28156 with
           | (prob,wl) ->
               let g =
                 let uu____28169 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____28179  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____28169  in
               ((let uu____28200 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____28200
                 then
                   let uu____28205 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____28205
>>>>>>> snap
=======
          (let uu____29715 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____29715
           then
             let uu____29720 = FStar_Syntax_Print.term_to_string t1  in
             let uu____29722 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____29720
               uu____29722
           else ());
          (let uu____29727 =
             let uu____29732 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____29732
              in
           match uu____29727 with
           | (prob,wl) ->
               let g =
                 let uu____29740 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____29748  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____29740  in
               ((let uu____29767 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____29767
                 then
                   let uu____29772 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____29772
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____29748 = try_teq true env t1 t2  in
        match uu____29748 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____29753 = FStar_TypeChecker_Env.get_range env  in
              let uu____29754 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____29753 uu____29754);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____29762 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____29762
              then
                let uu____29767 = FStar_Syntax_Print.term_to_string t1  in
                let uu____29769 = FStar_Syntax_Print.term_to_string t2  in
                let uu____29771 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____29767
                  uu____29769 uu____29771
=======
        let uu____28226 = try_teq true env t1 t2  in
        match uu____28226 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____28231 = FStar_TypeChecker_Env.get_range env  in
              let uu____28232 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____28231 uu____28232);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____28240 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____28240
              then
                let uu____28245 = FStar_Syntax_Print.term_to_string t1  in
                let uu____28247 = FStar_Syntax_Print.term_to_string t2  in
                let uu____28249 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____28245
                  uu____28247 uu____28249
>>>>>>> snap
=======
        let uu____29793 = try_teq true env t1 t2  in
        match uu____29793 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____29798 = FStar_TypeChecker_Env.get_range env  in
              let uu____29799 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____29798 uu____29799);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____29807 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____29807
              then
                let uu____29812 = FStar_Syntax_Print.term_to_string t1  in
                let uu____29814 = FStar_Syntax_Print.term_to_string t2  in
                let uu____29816 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____29812
                  uu____29814 uu____29816
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
          let uu____29797 = FStar_TypeChecker_Env.get_range env  in
          let uu____29798 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____29797 uu____29798
=======
          let uu____28275 = FStar_TypeChecker_Env.get_range env  in
          let uu____28276 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____28275 uu____28276
>>>>>>> snap
=======
          let uu____29842 = FStar_TypeChecker_Env.get_range env  in
          let uu____29843 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____29842 uu____29843
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
        (let uu____29827 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____29827
         then
           let uu____29832 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____29834 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____29832 uu____29834
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____29845 =
           let uu____29852 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____29852 "sub_comp"
            in
         match uu____29845 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____29865 =
                 FStar_Util.record_time
                   (fun uu____29877  ->
                      let uu____29878 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____29887  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____29878)
                  in
               match uu____29865 with
               | (r,ms) ->
                   ((let uu____29916 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____29916
                     then
                       let uu____29921 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____29923 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____29925 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____29921 uu____29923
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____29925
=======
        (let uu____28305 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____28305
         then
           let uu____28310 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____28312 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____28310 uu____28312
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____28323 =
           let uu____28330 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____28330 "sub_comp"
            in
         match uu____28323 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____28343 =
                 FStar_Util.record_time
                   (fun uu____28355  ->
                      let uu____28356 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____28367  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____28356)
                  in
               match uu____28343 with
               | (r,ms) ->
                   ((let uu____28398 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____28398
                     then
                       let uu____28403 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____28405 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____28407 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____28403 uu____28405
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____28407
>>>>>>> snap
=======
        (let uu____29872 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____29872
         then
           let uu____29877 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____29879 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____29877 uu____29879
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____29890 =
           let uu____29897 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____29897 "sub_comp"
            in
         match uu____29890 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____29910 =
                 FStar_Util.record_time
                   (fun uu____29922  ->
                      let uu____29923 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____29932  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____29923)
                  in
               match uu____29910 with
               | (r,ms) ->
                   ((let uu____29961 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____29961
                     then
                       let uu____29966 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____29968 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____29970 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____29966 uu____29968
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____29970
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
      fun uu____29963  ->
        match uu____29963 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____30006 =
                 let uu____30012 =
                   let uu____30014 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____30016 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____30014 uu____30016
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____30012)  in
               let uu____30020 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____30006 uu____30020)
               in
            let equiv1 v1 v' =
              let uu____30033 =
                let uu____30038 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____30039 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____30038, uu____30039)  in
              match uu____30033 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____30059 -> false  in
=======
      fun uu____28445  ->
        match uu____28445 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____28488 =
                 let uu____28494 =
                   let uu____28496 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____28498 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____28496 uu____28498
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____28494)  in
               let uu____28502 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____28488 uu____28502)
               in
            let equiv1 v1 v' =
              let uu____28515 =
                let uu____28520 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____28521 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____28520, uu____28521)  in
              match uu____28515 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____28541 -> false  in
>>>>>>> snap
=======
      fun uu____30008  ->
        match uu____30008 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____30051 =
                 let uu____30057 =
                   let uu____30059 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____30061 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____30059 uu____30061
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____30057)  in
               let uu____30065 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____30051 uu____30065)
               in
            let equiv1 v1 v' =
              let uu____30078 =
                let uu____30083 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____30084 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____30083, uu____30084)  in
              match uu____30078 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____30104 -> false  in
>>>>>>> snap
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
<<<<<<< HEAD
<<<<<<< HEAD
                      let uu____30090 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____30090 with
                      | FStar_Syntax_Syntax.U_unif uu____30097 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____30126  ->
                                    match uu____30126 with
                                    | (u,v') ->
                                        let uu____30135 = equiv1 v1 v'  in
                                        if uu____30135
                                        then
                                          let uu____30140 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____30140 then [] else [u])
=======
                      let uu____28572 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____28572 with
                      | FStar_Syntax_Syntax.U_unif uu____28579 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____28608  ->
                                    match uu____28608 with
                                    | (u,v') ->
                                        let uu____28617 = equiv1 v1 v'  in
                                        if uu____28617
                                        then
                                          let uu____28622 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____28622 then [] else [u])
>>>>>>> snap
=======
                      let uu____30135 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____30135 with
                      | FStar_Syntax_Syntax.U_unif uu____30142 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____30171  ->
                                    match uu____30171 with
                                    | (u,v') ->
                                        let uu____30180 = equiv1 v1 v'  in
                                        if uu____30180
                                        then
                                          let uu____30185 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____30185 then [] else [u])
>>>>>>> snap
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
<<<<<<< HEAD
<<<<<<< HEAD
                      | uu____30161 -> []))
               in
            let uu____30166 =
              let wl =
                let uu___3969_30170 = empty_worklist env  in
                {
                  attempting = (uu___3969_30170.attempting);
                  wl_deferred = (uu___3969_30170.wl_deferred);
                  ctr = (uu___3969_30170.ctr);
                  defer_ok = false;
                  smt_ok = (uu___3969_30170.smt_ok);
                  umax_heuristic_ok = (uu___3969_30170.umax_heuristic_ok);
                  tcenv = (uu___3969_30170.tcenv);
                  wl_implicits = (uu___3969_30170.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____30189  ->
                      match uu____30189 with
                      | (lb,v1) ->
                          let uu____30196 =
                            solve_universe_eq (~- Prims.int_one) wl lb v1  in
                          (match uu____30196 with
                           | USolved wl1 -> ()
                           | uu____30199 -> fail1 lb v1)))
               in
            let rec check_ineq uu____30210 =
              match uu____30210 with
=======
                      | uu____28643 -> []))
               in
            let uu____28648 =
              let wl =
                let uu___3798_28652 = empty_worklist env  in
                {
                  attempting = (uu___3798_28652.attempting);
                  wl_deferred = (uu___3798_28652.wl_deferred);
                  ctr = (uu___3798_28652.ctr);
                  defer_ok = false;
                  smt_ok = (uu___3798_28652.smt_ok);
                  umax_heuristic_ok = (uu___3798_28652.umax_heuristic_ok);
                  tcenv = (uu___3798_28652.tcenv);
                  wl_implicits = (uu___3798_28652.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____28671  ->
                      match uu____28671 with
                      | (lb,v1) ->
                          let uu____28678 =
                            solve_universe_eq (~- Prims.int_one) wl lb v1  in
                          (match uu____28678 with
                           | USolved wl1 -> ()
                           | uu____28681 -> fail1 lb v1)))
               in
            let rec check_ineq uu____28692 =
              match uu____28692 with
>>>>>>> snap
=======
                      | uu____30206 -> []))
               in
            let uu____30211 =
              let wl =
                let uu___3973_30215 = empty_worklist env  in
                {
                  attempting = (uu___3973_30215.attempting);
                  wl_deferred = (uu___3973_30215.wl_deferred);
                  ctr = (uu___3973_30215.ctr);
                  defer_ok = false;
                  smt_ok = (uu___3973_30215.smt_ok);
                  umax_heuristic_ok = (uu___3973_30215.umax_heuristic_ok);
                  tcenv = (uu___3973_30215.tcenv);
                  wl_implicits = (uu___3973_30215.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____30234  ->
                      match uu____30234 with
                      | (lb,v1) ->
                          let uu____30241 =
                            solve_universe_eq (~- Prims.int_one) wl lb v1  in
                          (match uu____30241 with
                           | USolved wl1 -> ()
                           | uu____30244 -> fail1 lb v1)))
               in
            let rec check_ineq uu____30255 =
              match uu____30255 with
>>>>>>> snap
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
<<<<<<< HEAD
<<<<<<< HEAD
                   | (FStar_Syntax_Syntax.U_zero ,uu____30222) -> true
=======
                   | (FStar_Syntax_Syntax.U_zero ,uu____28704) -> true
>>>>>>> snap
=======
                   | (FStar_Syntax_Syntax.U_zero ,uu____30267) -> true
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
                      uu____30246,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____30248,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____30259) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____30267,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____30276 -> false)
               in
            let uu____30282 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____30299  ->
                      match uu____30299 with
                      | (u,v1) ->
                          let uu____30307 = check_ineq (u, v1)  in
                          if uu____30307
                          then true
                          else
                            ((let uu____30315 =
=======
                      uu____28728,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____28730,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____28741) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____28749,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____28758 -> false)
               in
            let uu____28764 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____28781  ->
                      match uu____28781 with
                      | (u,v1) ->
                          let uu____28789 = check_ineq (u, v1)  in
                          if uu____28789
                          then true
                          else
                            ((let uu____28797 =
>>>>>>> snap
=======
                      uu____30291,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____30293,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____30304) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____30312,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____30321 -> false)
               in
            let uu____30327 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____30344  ->
                      match uu____30344 with
                      | (u,v1) ->
                          let uu____30352 = check_ineq (u, v1)  in
                          if uu____30352
                          then true
                          else
                            ((let uu____30360 =
>>>>>>> snap
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
<<<<<<< HEAD
<<<<<<< HEAD
                              if uu____30315
                              then
                                let uu____30320 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____30322 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____30320
                                  uu____30322
                              else ());
                             false)))
               in
            if uu____30282
            then ()
            else
              ((let uu____30332 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____30332
                then
                  ((let uu____30338 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____30338);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____30350 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____30350))
                else ());
               (let uu____30363 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____30363))
=======
                              if uu____28797
                              then
                                let uu____28802 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____28804 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____28802
                                  uu____28804
                              else ());
                             false)))
               in
            if uu____28764
            then ()
            else
              ((let uu____28814 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____28814
                then
                  ((let uu____28820 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____28820);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____28832 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____28832))
                else ());
               (let uu____28845 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____28845))
>>>>>>> snap
=======
                              if uu____30360
                              then
                                let uu____30365 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____30367 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____30365
                                  uu____30367
                              else ());
                             false)))
               in
            if uu____30327
            then ()
            else
              ((let uu____30377 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____30377
                then
                  ((let uu____30383 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____30383);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____30395 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____30395))
                else ());
               (let uu____30408 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____30408))
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
        let fail1 uu____30437 =
          match uu____30437 with
=======
        let fail1 uu____28919 =
          match uu____28919 with
>>>>>>> snap
=======
        let fail1 uu____30482 =
          match uu____30482 with
>>>>>>> snap
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
<<<<<<< HEAD
<<<<<<< HEAD
          let uu___4046_30463 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4046_30463.attempting);
            wl_deferred = (uu___4046_30463.wl_deferred);
            ctr = (uu___4046_30463.ctr);
            defer_ok;
            smt_ok = (uu___4046_30463.smt_ok);
            umax_heuristic_ok = (uu___4046_30463.umax_heuristic_ok);
            tcenv = (uu___4046_30463.tcenv);
            wl_implicits = (uu___4046_30463.wl_implicits)
          }  in
        (let uu____30466 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30466
         then
           let uu____30471 = FStar_Util.string_of_bool defer_ok  in
           let uu____30473 = wl_to_string wl  in
           let uu____30475 =
=======
          let uu___3875_28945 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___3875_28945.attempting);
            wl_deferred = (uu___3875_28945.wl_deferred);
            ctr = (uu___3875_28945.ctr);
            defer_ok;
            smt_ok = (uu___3875_28945.smt_ok);
            umax_heuristic_ok = (uu___3875_28945.umax_heuristic_ok);
            tcenv = (uu___3875_28945.tcenv);
            wl_implicits = (uu___3875_28945.wl_implicits)
          }  in
        (let uu____28948 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____28948
         then
           let uu____28953 = FStar_Util.string_of_bool defer_ok  in
           let uu____28955 = wl_to_string wl  in
           let uu____28957 =
>>>>>>> snap
=======
          let uu___4050_30508 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4050_30508.attempting);
            wl_deferred = (uu___4050_30508.wl_deferred);
            ctr = (uu___4050_30508.ctr);
            defer_ok;
            smt_ok = (uu___4050_30508.smt_ok);
            umax_heuristic_ok = (uu___4050_30508.umax_heuristic_ok);
            tcenv = (uu___4050_30508.tcenv);
            wl_implicits = (uu___4050_30508.wl_implicits)
          }  in
        (let uu____30511 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30511
         then
           let uu____30516 = FStar_Util.string_of_bool defer_ok  in
           let uu____30518 = wl_to_string wl  in
           let uu____30520 =
>>>>>>> snap
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Common.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
<<<<<<< HEAD
<<<<<<< HEAD
             uu____30471 uu____30473 uu____30475
         else ());
        (let g1 =
           let uu____30481 = solve_and_commit env wl fail1  in
           match uu____30481 with
           | FStar_Pervasives_Native.Some
               (uu____30488::uu____30489,uu____30490) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4061_30519 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4061_30519.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4061_30519.FStar_TypeChecker_Common.univ_ineqs);
=======
             uu____30516 uu____30518 uu____30520
         else ());
        (let g1 =
           let uu____30526 = solve_and_commit env wl fail1  in
           match uu____30526 with
           | FStar_Pervasives_Native.Some
               (uu____30533::uu____30534,uu____30535) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4065_30564 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4065_30564.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4065_30564.FStar_TypeChecker_Common.univ_ineqs);
>>>>>>> snap
                 FStar_TypeChecker_Common.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Common.implicits
                      imps)
               }
<<<<<<< HEAD
           | uu____30520 ->
=======
           | uu____30565 ->
>>>>>>> snap
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env
           g1.FStar_TypeChecker_Common.univ_ineqs;
<<<<<<< HEAD
         (let uu___4066_30529 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4066_30529.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4066_30529.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4066_30529.FStar_TypeChecker_Common.implicits)
=======
             uu____28953 uu____28955 uu____28957
         else ());
        (let g1 =
           let uu____28963 = solve_and_commit env wl fail1  in
           match uu____28963 with
           | FStar_Pervasives_Native.Some
               (uu____28970::uu____28971,uu____28972) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___3890_29001 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___3890_29001.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___3890_29001.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____29002 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___3895_29011 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___3895_29011.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___3895_29011.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___3895_29011.FStar_TypeChecker_Env.implicits)
>>>>>>> snap
=======
         (let uu___4070_30574 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4070_30574.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4070_30574.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4070_30574.FStar_TypeChecker_Common.implicits)
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
            let uu___4078_30606 = g1  in
=======
            let uu___3907_29088 = g1  in
>>>>>>> snap
=======
            let uu___4082_30651 = g1  in
>>>>>>> snap
            {
              FStar_TypeChecker_Common.guard_f =
                FStar_TypeChecker_Common.Trivial;
<<<<<<< HEAD
              FStar_TypeChecker_Common.deferred =
<<<<<<< HEAD
                (uu___4078_30606.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4078_30606.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___4078_30606.FStar_TypeChecker_Common.implicits)
            }  in
          let uu____30607 =
            let uu____30609 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____30609  in
          if uu____30607
=======
              FStar_TypeChecker_Env.deferred =
                (uu___3907_29088.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___3907_29088.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___3907_29088.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____29089 =
            let uu____29091 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____29091  in
          if uu____29089
>>>>>>> snap
=======
                (uu___4082_30651.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4082_30651.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___4082_30651.FStar_TypeChecker_Common.implicits)
            }  in
          let uu____30652 =
            let uu____30654 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____30654  in
          if uu____30652
>>>>>>> snap
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Common.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
<<<<<<< HEAD
<<<<<<< HEAD
                    (let uu____30621 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____30622 =
                       let uu____30624 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____30624
                        in
                     FStar_Errors.diag uu____30621 uu____30622)
=======
                    (let uu____29103 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____29104 =
                       let uu____29106 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____29106
                        in
                     FStar_Errors.diag uu____29103 uu____29104)
>>>>>>> snap
=======
                    (let uu____30666 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____30667 =
                       let uu____30669 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____30669
                        in
                     FStar_Errors.diag uu____30666 uu____30667)
>>>>>>> snap
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
<<<<<<< HEAD
<<<<<<< HEAD
                     (let uu____30632 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____30633 =
                        let uu____30635 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____30635
                         in
                      FStar_Errors.diag uu____30632 uu____30633)
                   else ();
                   (let uu____30641 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____30641
                      "discharge_guard'" env vc1);
                   (let uu____30643 =
                      FStar_TypeChecker_Common.check_trivial vc1  in
                    match uu____30643 with
=======
                     (let uu____29114 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____29115 =
                        let uu____29117 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____29117
                         in
                      FStar_Errors.diag uu____29114 uu____29115)
                   else ();
                   (let uu____29123 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____29123
                      "discharge_guard'" env vc1);
                   (let uu____29125 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____29125 with
>>>>>>> snap
=======
                     (let uu____30677 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____30678 =
                        let uu____30680 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____30680
                         in
                      FStar_Errors.diag uu____30677 uu____30678)
                   else ();
                   (let uu____30686 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____30686
                      "discharge_guard'" env vc1);
                   (let uu____30688 =
                      FStar_TypeChecker_Common.check_trivial vc1  in
                    match uu____30688 with
>>>>>>> snap
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
<<<<<<< HEAD
<<<<<<< HEAD
                             (let uu____30652 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____30653 =
                                let uu____30655 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____30655
                                 in
                              FStar_Errors.diag uu____30652 uu____30653)
=======
                             (let uu____29134 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____29135 =
                                let uu____29137 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____29137
                                 in
                              FStar_Errors.diag uu____29134 uu____29135)
>>>>>>> snap
=======
                             (let uu____30697 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____30698 =
                                let uu____30700 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____30700
                                 in
                              FStar_Errors.diag uu____30697 uu____30698)
>>>>>>> snap
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
<<<<<<< HEAD
<<<<<<< HEAD
                             (let uu____30665 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____30666 =
                                let uu____30668 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____30668
                                 in
                              FStar_Errors.diag uu____30665 uu____30666)
                           else ();
                           (let vcs =
                              let uu____30682 = FStar_Options.use_tactics ()
                                 in
                              if uu____30682
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____30704  ->
                                     (let uu____30706 =
=======
                             (let uu____29147 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____29148 =
                                let uu____29150 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____29150
                                 in
                              FStar_Errors.diag uu____29147 uu____29148)
                           else ();
                           (let vcs =
                              let uu____29164 = FStar_Options.use_tactics ()
                                 in
                              if uu____29164
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____29186  ->
                                     (let uu____29188 =
>>>>>>> snap
=======
                             (let uu____30710 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____30711 =
                                let uu____30713 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____30713
                                 in
                              FStar_Errors.diag uu____30710 uu____30711)
                           else ();
                           (let vcs =
                              let uu____30727 = FStar_Options.use_tactics ()
                                 in
                              if uu____30727
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____30749  ->
                                     (let uu____30751 =
>>>>>>> snap
                                        FStar_Options.set_options
                                          "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
<<<<<<< HEAD
<<<<<<< HEAD
                                        uu____30706);
=======
                                        uu____29188);
>>>>>>> snap
=======
                                        uu____30751);
>>>>>>> snap
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
<<<<<<< HEAD
<<<<<<< HEAD
                                           (fun uu____30750  ->
                                              match uu____30750 with
                                              | (env1,goal,opts) ->
                                                  let uu____30766 =
=======
                                           (fun uu____29232  ->
                                              match uu____29232 with
                                              | (env1,goal,opts) ->
                                                  let uu____29248 =
>>>>>>> snap
=======
                                           (fun uu____30795  ->
                                              match uu____30795 with
                                              | (env1,goal,opts) ->
                                                  let uu____30811 =
>>>>>>> snap
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
<<<<<<< HEAD
<<<<<<< HEAD
                                                  (env1, uu____30766, opts)))))
                              else
                                (let uu____30769 =
                                   let uu____30776 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____30776)  in
                                 [uu____30769])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____30809  ->
                                    match uu____30809 with
                                    | (env1,goal,opts) ->
                                        let uu____30819 =
                                          FStar_TypeChecker_Common.check_trivial
                                            goal
                                           in
                                        (match uu____30819 with
=======
                                                  (env1, uu____29248, opts)))))
                              else
                                (let uu____29251 =
                                   let uu____29258 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____29258)  in
                                 [uu____29251])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____29291  ->
                                    match uu____29291 with
                                    | (env1,goal,opts) ->
                                        let uu____29301 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____29301 with
>>>>>>> snap
=======
                                                  (env1, uu____30811, opts)))))
                              else
                                (let uu____30814 =
                                   let uu____30821 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____30821)  in
                                 [uu____30814])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____30854  ->
                                    match uu____30854 with
                                    | (env1,goal,opts) ->
                                        let uu____30864 =
                                          FStar_TypeChecker_Common.check_trivial
                                            goal
                                           in
                                        (match uu____30864 with
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
                                                (let uu____30830 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____30831 =
                                                   let uu____30833 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____30835 =
=======
                                                (let uu____29312 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____29313 =
                                                   let uu____29315 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____29317 =
>>>>>>> snap
=======
                                                (let uu____30875 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____30876 =
                                                   let uu____30878 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____30880 =
>>>>>>> snap
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
<<<<<<< HEAD
<<<<<<< HEAD
                                                     uu____30833 uu____30835
                                                    in
                                                 FStar_Errors.diag
                                                   uu____30830 uu____30831)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____30842 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____30843 =
                                                   let uu____30845 =
=======
                                                     uu____29315 uu____29317
                                                    in
                                                 FStar_Errors.diag
                                                   uu____29312 uu____29313)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____29324 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____29325 =
                                                   let uu____29327 =
>>>>>>> snap
=======
                                                     uu____30878 uu____30880
                                                    in
                                                 FStar_Errors.diag
                                                   uu____30875 uu____30876)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____30887 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____30888 =
                                                   let uu____30890 =
>>>>>>> snap
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
<<<<<<< HEAD
<<<<<<< HEAD
                                                     uu____30845
                                                    in
                                                 FStar_Errors.diag
                                                   uu____30842 uu____30843)
=======
                                                     uu____29327
                                                    in
                                                 FStar_Errors.diag
                                                   uu____29324 uu____29325)
>>>>>>> snap
=======
                                                     uu____30890
                                                    in
                                                 FStar_Errors.diag
                                                   uu____30887 uu____30888)
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____30863 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____30863 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____30872 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____30872
=======
      let uu____29345 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____29345 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____29354 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____29354
>>>>>>> snap
=======
      let uu____30908 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____30908 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____30917 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____30917
>>>>>>> snap
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____30886 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____30886 with
=======
      let uu____29368 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____29368 with
>>>>>>> snap
=======
      let uu____30931 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____30931 with
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____30916 = try_teq false env t1 t2  in
        match uu____30916 with
=======
        let uu____29398 = try_teq false env t1 t2  in
        match uu____29398 with
>>>>>>> snap
=======
        let uu____30961 = try_teq false env t1 t2  in
        match uu____30961 with
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
            let uu____30960 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____30960 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____30973 ->
                     let uu____30986 =
                       let uu____30987 = FStar_Syntax_Subst.compress r  in
                       uu____30987.FStar_Syntax_Syntax.n  in
                     (match uu____30986 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____30992) ->
                          unresolved ctx_u'
                      | uu____31009 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____31033 = acc  in
            match uu____31033 with
=======
            let uu____29442 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____29442 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____29455 ->
                     let uu____29468 =
                       let uu____29469 = FStar_Syntax_Subst.compress r  in
                       uu____29469.FStar_Syntax_Syntax.n  in
                     (match uu____29468 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____29474) ->
                          unresolved ctx_u'
                      | uu____29491 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____29515 = acc  in
            match uu____29515 with
>>>>>>> snap
=======
            let uu____31005 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____31005 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____31018 ->
                     let uu____31031 =
                       let uu____31032 = FStar_Syntax_Subst.compress r  in
                       uu____31032.FStar_Syntax_Syntax.n  in
                     (match uu____31031 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____31037) ->
                          unresolved ctx_u'
                      | uu____31054 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____31078 = acc  in
            match uu____31078 with
>>>>>>> snap
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
<<<<<<< HEAD
<<<<<<< HEAD
                     let uu____31052 = hd1  in
                     (match uu____31052 with
=======
                     let uu____31097 = hd1  in
                     (match uu____31097 with
>>>>>>> snap
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
=======
                     let uu____29534 = hd1  in
                     (match uu____29534 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;_} ->
>>>>>>> snap
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
<<<<<<< HEAD
<<<<<<< HEAD
                            (let uu____31063 = unresolved ctx_u  in
                             if uu____31063
=======
                            (let uu____29545 = unresolved ctx_u  in
                             if uu____29545
>>>>>>> snap
=======
                            (let uu____31108 = unresolved ctx_u  in
                             if uu____31108
>>>>>>> snap
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
<<<<<<< HEAD
<<<<<<< HEAD
                                   ((let uu____31087 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____31087
                                     then
                                       let uu____31091 =
=======
                                   ((let uu____29569 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____29569
                                     then
                                       let uu____29573 =
>>>>>>> snap
=======
                                   ((let uu____31132 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____31132
                                     then
                                       let uu____31136 =
>>>>>>> snap
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
<<<<<<< HEAD
<<<<<<< HEAD
                                         uu____31091
=======
                                         uu____29573
>>>>>>> snap
=======
                                         uu____31136
>>>>>>> snap
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
<<<<<<< HEAD
<<<<<<< HEAD
                                       let uu____31100 = teq_nosmt env1 t tm
                                          in
                                       match uu____31100 with
=======
                                       let uu____29582 = teq_nosmt env1 t tm
                                          in
                                       match uu____29582 with
>>>>>>> snap
=======
                                       let uu____31145 = teq_nosmt env1 t tm
                                          in
                                       match uu____31145 with
>>>>>>> snap
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
<<<<<<< HEAD
<<<<<<< HEAD
                                       let uu___4190_31110 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4190_31110.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4190_31110.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4190_31110.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4190_31110.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4190_31110.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4190_31110.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4190_31110.FStar_Syntax_Syntax.ctx_uvar_range);
=======
                                       let uu___4019_29592 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4019_29592.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4019_29592.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4019_29592.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4019_29592.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4019_29592.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4019_29592.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4019_29592.FStar_Syntax_Syntax.ctx_uvar_range);
>>>>>>> snap
=======
                                       let uu___4194_31155 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4194_31155.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4194_31155.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4194_31155.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4194_31155.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4194_31155.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4194_31155.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4194_31155.FStar_Syntax_Syntax.ctx_uvar_range);
>>>>>>> snap
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
<<<<<<< HEAD
<<<<<<< HEAD
                                       let uu___4193_31118 = hd1  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4193_31118.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4193_31118.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4193_31118.FStar_TypeChecker_Common.imp_range)
=======
                                       let uu___4022_29600 = hd1  in
                                       {
                                         FStar_TypeChecker_Env.imp_reason =
                                           (uu___4022_29600.FStar_TypeChecker_Env.imp_reason);
                                         FStar_TypeChecker_Env.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Env.imp_tm =
                                           (uu___4022_29600.FStar_TypeChecker_Env.imp_tm);
                                         FStar_TypeChecker_Env.imp_range =
                                           (uu___4022_29600.FStar_TypeChecker_Env.imp_range)
>>>>>>> snap
=======
                                       let uu___4197_31163 = hd1  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4197_31163.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4197_31163.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4197_31163.FStar_TypeChecker_Common.imp_range)
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
                                    let uu___4197_31129 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4197_31129.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4197_31129.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4197_31129.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4197_31129.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4197_31129.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4197_31129.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4197_31129.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4197_31129.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4197_31129.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___4197_31129.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4197_31129.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4197_31129.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4197_31129.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4197_31129.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4197_31129.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4197_31129.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4197_31129.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4197_31129.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4197_31129.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4197_31129.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4197_31129.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4197_31129.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4197_31129.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4197_31129.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4197_31129.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4197_31129.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4197_31129.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4197_31129.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4197_31129.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4197_31129.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4197_31129.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4197_31129.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4197_31129.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4197_31129.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                        (uu___4116_30300.FStar_TypeChecker_Env.synth_hook);
=======
                                        (uu___4196_31261.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4196_31261.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                                        (uu___4196_31262.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4196_31262.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                                        (uu___4185_31130.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4185_31130.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                                        (uu___4186_31054.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4186_31054.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                                        (uu___4197_31129.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4197_31129.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                                        (uu___4203_31176.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4203_31176.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> cp debugging an issue
=======
                                        (uu___4197_31129.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4197_31129.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> some more comments
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4197_31129.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4197_31129.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4197_31129.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4197_31129.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4197_31129.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4197_31129.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4197_31129.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                        (uu___4197_31129.FStar_TypeChecker_Env.strict_args_tab)
=======
                                        (uu___4025_29585.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4025_29585.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> snap
=======
                                        (uu___4203_31176.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4203_31176.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> cp debugging an issue
=======
                                        (uu___4197_31129.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4197_31129.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> some more comments
=======
                                    let uu___4026_29611 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4026_29611.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4026_29611.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4026_29611.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4026_29611.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4026_29611.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4026_29611.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4026_29611.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4026_29611.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4026_29611.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___4026_29611.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4026_29611.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4026_29611.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4026_29611.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4026_29611.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4026_29611.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4026_29611.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4026_29611.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4026_29611.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4026_29611.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4026_29611.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4026_29611.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4026_29611.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4026_29611.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4026_29611.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4026_29611.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4026_29611.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4026_29611.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4026_29611.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4026_29611.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4026_29611.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4026_29611.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4026_29611.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4026_29611.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4026_29611.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4026_29611.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4026_29611.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4026_29611.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4026_29611.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4026_29611.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4026_29611.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4026_29611.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4026_29611.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4026_29611.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4026_29611.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> snap
=======
                                    let uu___4201_31174 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4201_31174.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4201_31174.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4201_31174.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4201_31174.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4201_31174.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4201_31174.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4201_31174.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4201_31174.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4201_31174.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___4201_31174.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4201_31174.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4201_31174.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4201_31174.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4201_31174.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4201_31174.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4201_31174.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4201_31174.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4201_31174.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4201_31174.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4201_31174.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4201_31174.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4201_31174.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4201_31174.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4201_31174.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4201_31174.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4201_31174.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4201_31174.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4201_31174.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4201_31174.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4201_31174.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4201_31174.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4201_31174.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4201_31174.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4201_31174.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4201_31174.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4201_31174.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4201_31174.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4201_31174.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4201_31174.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4201_31174.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4201_31174.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4201_31174.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4201_31174.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4201_31174.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4201_31174.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> snap
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
<<<<<<< HEAD
<<<<<<< HEAD
                                      let uu___4202_31133 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4202_31133.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4202_31133.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4202_31133.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4202_31133.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4202_31133.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4202_31133.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4202_31133.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4202_31133.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4202_31133.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4202_31133.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___4202_31133.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4202_31133.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4202_31133.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4202_31133.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4202_31133.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4202_31133.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4202_31133.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4202_31133.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4202_31133.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4202_31133.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4202_31133.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4202_31133.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4202_31133.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4202_31133.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4202_31133.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4202_31133.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4202_31133.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4202_31133.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4202_31133.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4202_31133.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4202_31133.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4202_31133.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4202_31133.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4202_31133.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                          (uu___4121_30304.FStar_TypeChecker_Env.synth_hook);
=======
                                          (uu___4201_31265.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4201_31265.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                                          (uu___4201_31266.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4201_31266.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                                          (uu___4190_31134.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4190_31134.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                                          (uu___4191_31058.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4191_31058.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                                          (uu___4202_31133.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4202_31133.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                                          (uu___4208_31180.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4208_31180.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> cp debugging an issue
=======
                                          (uu___4202_31133.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4202_31133.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> some more comments
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4202_31133.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4202_31133.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4202_31133.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4202_31133.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4202_31133.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4202_31133.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4202_31133.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                          (uu___4202_31133.FStar_TypeChecker_Env.strict_args_tab)
=======
                                          (uu___4030_29589.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4030_29589.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> snap
=======
                                          (uu___4208_31180.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4208_31180.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> cp debugging an issue
=======
                                          (uu___4202_31133.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4202_31133.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> some more comments
                                      }
                                    else env1  in
                                  (let uu____31138 =
=======
                                      let uu___4031_29615 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4031_29615.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4031_29615.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4031_29615.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4031_29615.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4031_29615.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4031_29615.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4031_29615.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4031_29615.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4031_29615.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4031_29615.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___4031_29615.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4031_29615.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4031_29615.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4031_29615.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4031_29615.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4031_29615.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4031_29615.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4031_29615.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4031_29615.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4031_29615.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4031_29615.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4031_29615.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4031_29615.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4031_29615.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4031_29615.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4031_29615.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4031_29615.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4031_29615.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4031_29615.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4031_29615.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4031_29615.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4031_29615.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4031_29615.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4031_29615.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4031_29615.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4031_29615.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4031_29615.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4031_29615.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4031_29615.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4031_29615.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4031_29615.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4031_29615.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4031_29615.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4031_29615.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____29620 =
>>>>>>> snap
=======
                                      let uu___4206_31178 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4206_31178.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4206_31178.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4206_31178.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4206_31178.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4206_31178.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4206_31178.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4206_31178.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4206_31178.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4206_31178.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4206_31178.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___4206_31178.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4206_31178.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4206_31178.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4206_31178.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4206_31178.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4206_31178.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4206_31178.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4206_31178.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4206_31178.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4206_31178.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4206_31178.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4206_31178.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4206_31178.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4206_31178.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4206_31178.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4206_31178.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4206_31178.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4206_31178.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4206_31178.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4206_31178.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4206_31178.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4206_31178.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4206_31178.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4206_31178.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4206_31178.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4206_31178.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4206_31178.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4206_31178.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4206_31178.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4206_31178.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4206_31178.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4206_31178.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4206_31178.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4206_31178.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4206_31178.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____31183 =
>>>>>>> snap
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
<<<<<<< HEAD
<<<<<<< HEAD
                                   if uu____31138
                                   then
                                     let uu____31143 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____31145 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____31147 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____31149 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____31143 uu____31145 uu____31147
                                       reason uu____31149
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4208_31156  ->
=======
                                   if uu____29620
                                   then
                                     let uu____29625 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____29627 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____29629 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____29631 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____29625 uu____29627 uu____29629
                                       reason uu____29631
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4037_29638  ->
>>>>>>> snap
=======
                                   if uu____31183
                                   then
                                     let uu____31188 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____31190 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____31192 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____31194 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____31188 uu____31190 uu____31192
                                       reason uu____31194
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4212_31201  ->
>>>>>>> snap
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
<<<<<<< HEAD
<<<<<<< HEAD
                                         ((let uu____31163 =
                                             let uu____31173 =
                                               let uu____31181 =
                                                 let uu____31183 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____31185 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____31187 =
=======
                                         ((let uu____29645 =
                                             let uu____29655 =
                                               let uu____29663 =
                                                 let uu____29665 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____29667 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____29669 =
>>>>>>> snap
=======
                                         ((let uu____31208 =
                                             let uu____31218 =
                                               let uu____31226 =
                                                 let uu____31228 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____31230 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____31232 =
>>>>>>> snap
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
<<<<<<< HEAD
<<<<<<< HEAD
                                                   uu____31183 uu____31185
                                                   uu____31187
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____31181, r)
                                                in
                                             [uu____31173]  in
                                           FStar_Errors.add_errors
                                             uu____31163);
=======
                                                   uu____29665 uu____29667
                                                   uu____29669
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____29663, r)
                                                in
                                             [uu____29655]  in
                                           FStar_Errors.add_errors
                                             uu____29645);
>>>>>>> snap
=======
                                                   uu____31228 uu____31230
                                                   uu____31232
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____31226, r)
                                                in
                                             [uu____31218]  in
                                           FStar_Errors.add_errors
                                             uu____31208);
>>>>>>> snap
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
<<<<<<< HEAD
<<<<<<< HEAD
                                       let uu___4216_31207 = g1  in
=======
                                       let uu___4045_29689 = g1  in
>>>>>>> snap
=======
                                       let uu___4220_31252 = g1  in
>>>>>>> snap
                                       {
                                         FStar_TypeChecker_Common.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
<<<<<<< HEAD
                                         FStar_TypeChecker_Common.deferred =
<<<<<<< HEAD
                                           (uu___4216_31207.FStar_TypeChecker_Common.deferred);
                                         FStar_TypeChecker_Common.univ_ineqs
                                           =
                                           (uu___4216_31207.FStar_TypeChecker_Common.univ_ineqs);
                                         FStar_TypeChecker_Common.implicits =
                                           (uu___4216_31207.FStar_TypeChecker_Common.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____31211 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____31222  ->
                                               let uu____31223 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____31225 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____31227 =
=======
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___4045_29689.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___4045_29689.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___4045_29689.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____29693 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____29704  ->
                                               let uu____29705 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____29707 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____29709 =
>>>>>>> snap
=======
                                           (uu___4220_31252.FStar_TypeChecker_Common.deferred);
                                         FStar_TypeChecker_Common.univ_ineqs
                                           =
                                           (uu___4220_31252.FStar_TypeChecker_Common.univ_ineqs);
                                         FStar_TypeChecker_Common.implicits =
                                           (uu___4220_31252.FStar_TypeChecker_Common.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____31256 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____31267  ->
                                               let uu____31268 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____31270 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____31272 =
>>>>>>> snap
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
<<<<<<< HEAD
<<<<<<< HEAD
                                                 uu____31223 uu____31225
                                                 reason uu____31227)) env2 g2
                                         true
                                        in
                                     match uu____31211 with
=======
                                                 uu____29705 uu____29707
                                                 reason uu____29709)) env2 g2
                                         true
                                        in
                                     match uu____29693 with
>>>>>>> snap
=======
                                                 uu____31268 uu____31270
                                                 reason uu____31272)) env2 g2
                                         true
                                        in
                                     match uu____31256 with
>>>>>>> snap
                                     | FStar_Pervasives_Native.Some g3 -> g3
                                     | FStar_Pervasives_Native.None  ->
                                         failwith
                                           "Impossible, with use_smt = true, discharge_guard' should never have returned None"
                                      in
                                   until_fixpoint
                                     ((FStar_List.append
                                         g'.FStar_TypeChecker_Common.implicits
                                         out), true) tl1)))))
             in
<<<<<<< HEAD
<<<<<<< HEAD
          let uu___4224_31235 = g  in
          let uu____31236 =
=======
          let uu___4228_31280 = g  in
          let uu____31281 =
>>>>>>> snap
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
<<<<<<< HEAD
              (uu___4224_31235.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4224_31235.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4224_31235.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____31236
=======
          let uu___4053_29717 = g  in
          let uu____29718 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4053_29717.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4053_29717.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___4053_29717.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____29718
>>>>>>> snap
=======
              (uu___4228_31280.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4228_31280.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4228_31280.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____31281
>>>>>>> snap
          }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
<<<<<<< HEAD
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> resolve_implicits' env true false g 
=======
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      resolve_implicits' env
        ((Prims.op_Negation env.FStar_TypeChecker_Env.phase1) &&
           (Prims.op_Negation env.FStar_TypeChecker_Env.lax)) false g
  
>>>>>>> snap
let (resolve_implicits_tac :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> resolve_implicits' env false true g 
let (force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.guard_t -> unit) =
  fun env  ->
    fun g  ->
      let g1 =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
=======
>>>>>>> snap
        let uu____31409 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____31409 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
<<<<<<< HEAD
<<<<<<< HEAD
          let uu____30449 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____30449
      | imp::uu____30451 ->
          let uu____30454 =
            let uu____30460 =
              let uu____30462 =
=======
        let uu____29734 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____29734 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____29735 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____29735
      | imp::uu____29737 ->
          let uu____29740 =
            let uu____29746 =
              let uu____29748 =
>>>>>>> snap
=======
        let uu____29760 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____29760 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____29761 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____29761
      | imp::uu____29763 ->
          let uu____29766 =
            let uu____29772 =
              let uu____29774 =
>>>>>>> snap
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
<<<<<<< HEAD
<<<<<<< HEAD
              let uu____30464 =
=======
              let uu____29750 =
>>>>>>> snap
=======
              let uu____29776 =
>>>>>>> snap
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
<<<<<<< HEAD
<<<<<<< HEAD
                uu____30462 uu____30464
                imp.FStar_TypeChecker_Common.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____30460)
             in
          FStar_Errors.raise_error uu____30454
            imp.FStar_TypeChecker_Common.imp_range
=======
=======
>>>>>>> snap
          let uu____31410 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____31410
      | imp::uu____31412 ->
          let uu____31415 =
=======
        let uu____31277 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____31277 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
          let uu____31278 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____31278
      | imp::uu____31280 ->
          let uu____31283 =
>>>>>>> snap
=======
        let uu____31201 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____31201 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
          let uu____31202 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____31202
      | imp::uu____31204 ->
          let uu____31207 =
>>>>>>> snap
=======
        let uu____31276 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____31276 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
          let uu____31277 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____31277
      | imp::uu____31279 ->
          let uu____31282 =
>>>>>>> snap
=======
        let uu____31323 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____31323 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
          let uu____31324 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____31324
      | imp::uu____31326 ->
          let uu____31329 =
>>>>>>> cp debugging an issue
=======
        let uu____31276 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____31276 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
          let uu____31277 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____31277
      | imp::uu____31279 ->
          let uu____31282 =
>>>>>>> some more comments
            FStar_TypeChecker_Env.lookup_attr env
              FStar_Parser_Const.resolve_implicits_attr_string
             in
          (match uu____31282 with
           | {
               FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                 (uu____31285,lid::[]);
               FStar_Syntax_Syntax.sigrng = uu____31287;
               FStar_Syntax_Syntax.sigquals = uu____31288;
               FStar_Syntax_Syntax.sigmeta = uu____31289;
               FStar_Syntax_Syntax.sigattrs = uu____31290;_}::uu____31291 ->
=======
        let uu____31321 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____31321 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
          let uu____31322 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____31322
      | imp::uu____31324 ->
          let uu____31327 =
            FStar_TypeChecker_Env.lookup_attr env
              FStar_Parser_Const.resolve_implicits_attr_string
             in
          (match uu____31327 with
           | {
               FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                 (uu____31330,lid::[]);
               FStar_Syntax_Syntax.sigrng = uu____31332;
               FStar_Syntax_Syntax.sigquals = uu____31333;
               FStar_Syntax_Syntax.sigmeta = uu____31334;
               FStar_Syntax_Syntax.sigattrs = uu____31335;_}::uu____31336 ->
>>>>>>> snap
               let qn = FStar_TypeChecker_Env.lookup_qname env lid  in
               let fv =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   (FStar_Syntax_Syntax.Delta_constant_at_level
                      Prims.int_zero) FStar_Pervasives_Native.None
                  in
               let dd =
<<<<<<< HEAD
                 let uu____31304 =
                   FStar_TypeChecker_Env.delta_depth_of_qninfo fv qn  in
                 match uu____31304 with
=======
                 let uu____31349 =
                   FStar_TypeChecker_Env.delta_depth_of_qninfo fv qn  in
                 match uu____31349 with
>>>>>>> snap
                 | FStar_Pervasives_Native.Some dd -> dd
                 | FStar_Pervasives_Native.None  -> failwith "Expected a dd"
                  in
               let term =
<<<<<<< HEAD
                 let uu____31310 =
                   FStar_Syntax_Syntax.lid_as_fv lid dd
                     FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____31310  in
               (env.FStar_TypeChecker_Env.try_solve_implicits_hook env term
                  g1.FStar_TypeChecker_Common.implicits;
                (let uu____31312 = discharge_guard env g1  in
                 FStar_All.pipe_left (fun a3  -> ()) uu____31312))
           | uu____31313 ->
               let uu____31316 =
                 let uu____31322 =
                   let uu____31324 =
                     FStar_Syntax_Print.uvar_to_string
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   let uu____31326 =
=======
                 let uu____31355 =
                   FStar_Syntax_Syntax.lid_as_fv lid dd
                     FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____31355  in
               (env.FStar_TypeChecker_Env.try_solve_implicits_hook env term
                  g1.FStar_TypeChecker_Common.implicits;
                (let uu____31357 = discharge_guard env g1  in
                 FStar_All.pipe_left (fun a3  -> ()) uu____31357))
           | uu____31358 ->
               let uu____31361 =
                 let uu____31367 =
                   let uu____31369 =
                     FStar_Syntax_Print.uvar_to_string
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   let uu____31371 =
>>>>>>> snap
                     FStar_TypeChecker_Normalize.term_to_string env
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                      in
                   FStar_Util.format3
                     "Failed to resolve implicit argument %s of type %s introduced for %s"
<<<<<<< HEAD
                     uu____31324 uu____31326
                     imp.FStar_TypeChecker_Common.imp_reason
                    in
                 (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                   uu____31322)
                  in
               FStar_Errors.raise_error uu____31316
=======
                     uu____31369 uu____31371
                     imp.FStar_TypeChecker_Common.imp_reason
                    in
                 (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                   uu____31367)
                  in
               FStar_Errors.raise_error uu____31361
>>>>>>> snap
                 imp.FStar_TypeChecker_Common.imp_range)
>>>>>>> snap
=======
                uu____29748 uu____29750 imp.FStar_TypeChecker_Env.imp_reason
=======
                uu____29774 uu____29776 imp.FStar_TypeChecker_Env.imp_reason
>>>>>>> snap
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____29772)
             in
          FStar_Errors.raise_error uu____29766
            imp.FStar_TypeChecker_Env.imp_range
>>>>>>> snap
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____30486 = teq_nosmt env t1 t2  in
        match uu____30486 with
=======
        let uu____31481 = teq_nosmt env t1 t2  in
        match uu____31481 with
>>>>>>> snap
=======
        let uu____29772 = teq_nosmt env t1 t2  in
        match uu____29772 with
>>>>>>> snap
=======
        let uu____31481 = teq_nosmt env t1 t2  in
        match uu____31481 with
>>>>>>> snap
=======
        let uu____31349 = teq_nosmt env t1 t2  in
        match uu____31349 with
>>>>>>> snap
=======
        let uu____31273 = teq_nosmt env t1 t2  in
        match uu____31273 with
>>>>>>> snap
=======
        let uu____31348 = teq_nosmt env t1 t2  in
        match uu____31348 with
>>>>>>> snap
=======
        let uu____31395 = teq_nosmt env t1 t2  in
        match uu____31395 with
>>>>>>> cp debugging an issue
=======
        let uu____31348 = teq_nosmt env t1 t2  in
        match uu____31348 with
>>>>>>> some more comments
=======
        let uu____29798 = teq_nosmt env t1 t2  in
        match uu____29798 with
>>>>>>> snap
=======
        let uu____31393 = teq_nosmt env t1 t2  in
        match uu____31393 with
>>>>>>> snap
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
      let uu___4165_30505 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4165_30505.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred =
          (uu___4165_30505.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4165_30505.FStar_TypeChecker_Common.implicits)
=======
=======
>>>>>>> snap
      let uu___4266_31500 = FStar_TypeChecker_Common.trivial_guard  in
=======
      let uu___4255_31368 = FStar_TypeChecker_Common.trivial_guard  in
>>>>>>> snap
=======
      let uu___4256_31292 = FStar_TypeChecker_Common.trivial_guard  in
>>>>>>> snap
=======
      let uu___4267_31367 = FStar_TypeChecker_Common.trivial_guard  in
>>>>>>> snap
=======
      let uu___4273_31414 = FStar_TypeChecker_Common.trivial_guard  in
>>>>>>> cp debugging an issue
=======
      let uu___4267_31367 = FStar_TypeChecker_Common.trivial_guard  in
>>>>>>> some more comments
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4267_31367.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred =
          (uu___4267_31367.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
          (uu___4266_31500.FStar_TypeChecker_Common.implicits)
<<<<<<< HEAD
>>>>>>> snap
=======
      let uu___4074_29791 = FStar_TypeChecker_Env.trivial_guard  in
=======
      let uu___4075_29817 = FStar_TypeChecker_Env.trivial_guard  in
>>>>>>> snap
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___4075_29817.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___4075_29817.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
<<<<<<< HEAD
          (uu___4074_29791.FStar_TypeChecker_Env.implicits)
>>>>>>> snap
=======
>>>>>>> snap
=======
          (uu___4255_31368.FStar_TypeChecker_Common.implicits)
>>>>>>> snap
=======
          (uu___4256_31292.FStar_TypeChecker_Common.implicits)
>>>>>>> snap
=======
          (uu___4267_31367.FStar_TypeChecker_Common.implicits)
>>>>>>> snap
=======
          (uu___4273_31414.FStar_TypeChecker_Common.implicits)
>>>>>>> cp debugging an issue
=======
          (uu___4267_31367.FStar_TypeChecker_Common.implicits)
>>>>>>> some more comments
=======
          (uu___4075_29817.FStar_TypeChecker_Env.implicits)
>>>>>>> snap
=======
      let uu___4271_31412 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4271_31412.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred =
          (uu___4271_31412.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4271_31412.FStar_TypeChecker_Common.implicits)
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        (let uu____30541 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30541
         then
           let uu____30546 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____30548 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____30546
             uu____30548
         else ());
        (let uu____30553 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____30553 with
         | (prob,x,wl) ->
             let g =
               let uu____30572 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30581  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30572  in
             ((let uu____30600 =
=======
        (let uu____31536 =
=======
        (let uu____31404 =
>>>>>>> snap
=======
        (let uu____31328 =
>>>>>>> snap
=======
        (let uu____31403 =
>>>>>>> snap
=======
        (let uu____31450 =
>>>>>>> cp debugging an issue
=======
        (let uu____31403 =
>>>>>>> some more comments
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31403
         then
           let uu____31408 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31410 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____31408
             uu____31410
         else ());
        (let uu____31415 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31415 with
         | (prob,x,wl) ->
             let g =
               let uu____31434 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____31443  -> FStar_Pervasives_Native.None)
                  in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
               FStar_All.pipe_left (with_guard env prob) uu____31567  in
             ((let uu____31595 =
>>>>>>> snap
=======
        (let uu____29827 =
=======
        (let uu____29853 =
>>>>>>> snap
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____29853
         then
           let uu____29858 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____29860 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____29858
             uu____29860
         else ());
        (let uu____29865 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____29865 with
         | (prob,x,wl) ->
             let g =
               let uu____29884 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____29895  -> FStar_Pervasives_Native.None)
                  in
<<<<<<< HEAD
               FStar_All.pipe_left (with_guard env prob) uu____29858  in
             ((let uu____29890 =
>>>>>>> snap
=======
        (let uu____31536 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31536
         then
           let uu____31541 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31543 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____31541
             uu____31543
         else ());
        (let uu____31548 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31548 with
         | (prob,x,wl) ->
             let g =
               let uu____31567 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____31576  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31567  in
             ((let uu____31595 =
>>>>>>> snap
=======
               FStar_All.pipe_left (with_guard env prob) uu____31435  in
             ((let uu____31463 =
>>>>>>> snap
=======
               FStar_All.pipe_left (with_guard env prob) uu____31359  in
             ((let uu____31387 =
>>>>>>> snap
=======
               FStar_All.pipe_left (with_guard env prob) uu____31434  in
             ((let uu____31462 =
>>>>>>> snap
=======
               FStar_All.pipe_left (with_guard env prob) uu____31481  in
             ((let uu____31509 =
>>>>>>> cp debugging an issue
=======
               FStar_All.pipe_left (with_guard env prob) uu____31434  in
             ((let uu____31462 =
>>>>>>> some more comments
=======
               FStar_All.pipe_left (with_guard env prob) uu____29884  in
             ((let uu____29916 =
>>>>>>> snap
=======
        (let uu____31448 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31448
         then
           let uu____31453 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31455 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____31453
             uu____31455
         else ());
        (let uu____31460 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31460 with
         | (prob,x,wl) ->
             let g =
               let uu____31479 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____31488  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31479  in
             ((let uu____31507 =
>>>>>>> snap
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
               if uu____30600
               then
                 let uu____30605 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____30607 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____30609 =
                   let uu____30611 = FStar_Util.must g  in
                   guard_to_string env uu____30611  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____30605 uu____30607 uu____30609
=======
               if uu____31595
               then
                 let uu____31600 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____31602 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____31604 =
                   let uu____31606 = FStar_Util.must g  in
                   guard_to_string env uu____31606  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____31600 uu____31602 uu____31604
>>>>>>> snap
=======
               if uu____29890
=======
               if uu____29916
>>>>>>> snap
               then
                 let uu____29921 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____29923 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____29925 =
                   let uu____29927 = FStar_Util.must g  in
                   guard_to_string env uu____29927  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
<<<<<<< HEAD
                   uu____29895 uu____29897 uu____29899
>>>>>>> snap
=======
               if uu____31595
=======
               if uu____31463
>>>>>>> snap
=======
               if uu____31387
>>>>>>> snap
=======
               if uu____31462
>>>>>>> snap
=======
               if uu____31509
>>>>>>> cp debugging an issue
=======
               if uu____31462
>>>>>>> some more comments
               then
                 let uu____31467 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____31469 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____31471 =
                   let uu____31473 = FStar_Util.must g  in
                   guard_to_string env uu____31473  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                   uu____31600 uu____31602 uu____31604
>>>>>>> snap
=======
                   uu____31468 uu____31470 uu____31472
>>>>>>> snap
=======
                   uu____31392 uu____31394 uu____31396
>>>>>>> snap
=======
                   uu____31467 uu____31469 uu____31471
>>>>>>> snap
=======
                   uu____31514 uu____31516 uu____31518
>>>>>>> cp debugging an issue
=======
                   uu____31467 uu____31469 uu____31471
>>>>>>> some more comments
=======
                   uu____29921 uu____29923 uu____29925
>>>>>>> snap
=======
               if uu____31507
               then
                 let uu____31512 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____31514 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____31516 =
                   let uu____31518 = FStar_Util.must g  in
                   guard_to_string env uu____31518  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____31512 uu____31514 uu____31516
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____30648 = check_subtyping env t1 t2  in
        match uu____30648 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____30667 =
              let uu____30668 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____30668 g  in
            FStar_Pervasives_Native.Some uu____30667
=======
        let uu____31643 = check_subtyping env t1 t2  in
        match uu____31643 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31662 =
              let uu____31663 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____31663 g  in
            FStar_Pervasives_Native.Some uu____31662
>>>>>>> snap
=======
        let uu____29938 = check_subtyping env t1 t2  in
        match uu____29938 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____29957 =
              let uu____29958 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____29958 g  in
            FStar_Pervasives_Native.Some uu____29957
>>>>>>> snap
=======
        let uu____31643 = check_subtyping env t1 t2  in
        match uu____31643 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31662 =
              let uu____31663 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____31663 g  in
            FStar_Pervasives_Native.Some uu____31662
>>>>>>> snap
=======
        let uu____31511 = check_subtyping env t1 t2  in
        match uu____31511 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31530 =
              let uu____31531 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____31531 g  in
            FStar_Pervasives_Native.Some uu____31530
>>>>>>> snap
=======
        let uu____31435 = check_subtyping env t1 t2  in
        match uu____31435 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31454 =
              let uu____31455 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____31455 g  in
            FStar_Pervasives_Native.Some uu____31454
>>>>>>> snap
=======
        let uu____31510 = check_subtyping env t1 t2  in
        match uu____31510 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31529 =
              let uu____31530 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____31530 g  in
            FStar_Pervasives_Native.Some uu____31529
>>>>>>> snap
=======
        let uu____31557 = check_subtyping env t1 t2  in
        match uu____31557 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31576 =
              let uu____31577 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____31577 g  in
            FStar_Pervasives_Native.Some uu____31576
>>>>>>> cp debugging an issue
=======
        let uu____31510 = check_subtyping env t1 t2  in
        match uu____31510 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31529 =
              let uu____31530 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____31530 g  in
            FStar_Pervasives_Native.Some uu____31529
>>>>>>> some more comments
=======
        let uu____29964 = check_subtyping env t1 t2  in
        match uu____29964 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____29983 =
              let uu____29984 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____29984 g  in
            FStar_Pervasives_Native.Some uu____29983
>>>>>>> snap
=======
        let uu____31555 = check_subtyping env t1 t2  in
        match uu____31555 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31574 =
              let uu____31575 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____31575 g  in
            FStar_Pervasives_Native.Some uu____31574
>>>>>>> snap
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____30687 = check_subtyping env t1 t2  in
        match uu____30687 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____30706 =
              let uu____30707 =
                let uu____30708 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____30708]  in
              FStar_TypeChecker_Env.close_guard env uu____30707 g  in
            FStar_Pervasives_Native.Some uu____30706
=======
        let uu____31682 = check_subtyping env t1 t2  in
        match uu____31682 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
=======
        let uu____31682 = check_subtyping env t1 t2  in
        match uu____31682 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
>>>>>>> snap
            let uu____31701 =
              let uu____31702 =
                let uu____31703 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____31703]  in
              FStar_TypeChecker_Env.close_guard env uu____31702 g  in
            FStar_Pervasives_Native.Some uu____31701
<<<<<<< HEAD
>>>>>>> snap
=======
        let uu____29977 = check_subtyping env t1 t2  in
        match uu____29977 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____29996 =
              let uu____29997 =
                let uu____29998 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____29998]  in
              FStar_TypeChecker_Env.close_guard env uu____29997 g  in
            FStar_Pervasives_Native.Some uu____29996
>>>>>>> snap
=======
>>>>>>> snap
=======
        let uu____31550 = check_subtyping env t1 t2  in
        match uu____31550 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31569 =
              let uu____31570 =
                let uu____31571 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____31571]  in
              FStar_TypeChecker_Env.close_guard env uu____31570 g  in
            FStar_Pervasives_Native.Some uu____31569
>>>>>>> snap
=======
        let uu____31474 = check_subtyping env t1 t2  in
        match uu____31474 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31493 =
              let uu____31494 =
                let uu____31495 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____31495]  in
              FStar_TypeChecker_Env.close_guard env uu____31494 g  in
            FStar_Pervasives_Native.Some uu____31493
>>>>>>> snap
=======
        let uu____31549 = check_subtyping env t1 t2  in
        match uu____31549 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31568 =
              let uu____31569 =
                let uu____31570 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____31570]  in
              FStar_TypeChecker_Env.close_guard env uu____31569 g  in
            FStar_Pervasives_Native.Some uu____31568
>>>>>>> snap
=======
        let uu____31596 = check_subtyping env t1 t2  in
        match uu____31596 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31615 =
              let uu____31616 =
                let uu____31617 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____31617]  in
              FStar_TypeChecker_Env.close_guard env uu____31616 g  in
            FStar_Pervasives_Native.Some uu____31615
>>>>>>> cp debugging an issue
=======
        let uu____31549 = check_subtyping env t1 t2  in
        match uu____31549 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31568 =
              let uu____31569 =
                let uu____31570 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____31570]  in
              FStar_TypeChecker_Env.close_guard env uu____31569 g  in
            FStar_Pervasives_Native.Some uu____31568
>>>>>>> some more comments
=======
        let uu____30003 = check_subtyping env t1 t2  in
        match uu____30003 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____30022 =
              let uu____30023 =
                let uu____30024 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____30024]  in
              FStar_TypeChecker_Env.close_guard env uu____30023 g  in
            FStar_Pervasives_Native.Some uu____30022
>>>>>>> snap
=======
        let uu____31594 = check_subtyping env t1 t2  in
        match uu____31594 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31613 =
              let uu____31614 =
                let uu____31615 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____31615]  in
              FStar_TypeChecker_Env.close_guard env uu____31614 g  in
            FStar_Pervasives_Native.Some uu____31613
>>>>>>> snap
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        (let uu____30746 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30746
         then
           let uu____30751 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____30753 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____30751
             uu____30753
         else ());
        (let uu____30758 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____30758 with
         | (prob,x,wl) ->
             let g =
               let uu____30773 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____30782  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30773  in
=======
        (let uu____31741 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31741
         then
           let uu____31746 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31748 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____31746
             uu____31748
         else ());
        (let uu____31753 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31753 with
         | (prob,x,wl) ->
             let g =
               let uu____31768 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____31777  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31768  in
>>>>>>> snap
=======
        (let uu____30036 =
=======
        (let uu____30062 =
>>>>>>> snap
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30062
         then
           let uu____30067 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____30069 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____30067
             uu____30069
         else ());
        (let uu____30074 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____30074 with
         | (prob,x,wl) ->
             let g =
               let uu____30089 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____30100  -> FStar_Pervasives_Native.None)
                  in
<<<<<<< HEAD
               FStar_All.pipe_left (with_guard env prob) uu____30063  in
>>>>>>> snap
=======
        (let uu____31741 =
=======
        (let uu____31609 =
>>>>>>> snap
=======
        (let uu____31533 =
>>>>>>> snap
=======
        (let uu____31608 =
>>>>>>> snap
=======
        (let uu____31655 =
>>>>>>> cp debugging an issue
=======
        (let uu____31608 =
>>>>>>> some more comments
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31608
         then
           let uu____31613 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31615 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____31613
             uu____31615
         else ());
        (let uu____31620 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31620 with
         | (prob,x,wl) ->
             let g =
               let uu____31635 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____31644  -> FStar_Pervasives_Native.None)
                  in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
               FStar_All.pipe_left (with_guard env prob) uu____31768  in
>>>>>>> snap
=======
               FStar_All.pipe_left (with_guard env prob) uu____31636  in
>>>>>>> snap
=======
               FStar_All.pipe_left (with_guard env prob) uu____31560  in
>>>>>>> snap
=======
               FStar_All.pipe_left (with_guard env prob) uu____31635  in
>>>>>>> snap
=======
               FStar_All.pipe_left (with_guard env prob) uu____31682  in
>>>>>>> cp debugging an issue
=======
               FStar_All.pipe_left (with_guard env prob) uu____31635  in
>>>>>>> some more comments
=======
               FStar_All.pipe_left (with_guard env prob) uu____30089  in
>>>>>>> snap
=======
        (let uu____31653 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31653
         then
           let uu____31658 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31660 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____31658
             uu____31660
         else ());
        (let uu____31665 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31665 with
         | (prob,x,wl) ->
             let g =
               let uu____31680 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____31689  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31680  in
>>>>>>> snap
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                    let uu____30804 =
                      let uu____30805 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____30805]  in
                    FStar_TypeChecker_Env.close_guard env uu____30804 g1  in
=======
=======
>>>>>>> snap
                    let uu____31799 =
                      let uu____31800 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____31800]  in
                    FStar_TypeChecker_Env.close_guard env uu____31799 g1  in
<<<<<<< HEAD
>>>>>>> snap
=======
                    let uu____30098 =
                      let uu____30099 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____30099]  in
                    FStar_TypeChecker_Env.close_guard env uu____30098 g1  in
>>>>>>> snap
=======
>>>>>>> snap
=======
                    let uu____31667 =
                      let uu____31668 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____31668]  in
                    FStar_TypeChecker_Env.close_guard env uu____31667 g1  in
>>>>>>> snap
=======
                    let uu____31591 =
                      let uu____31592 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____31592]  in
                    FStar_TypeChecker_Env.close_guard env uu____31591 g1  in
>>>>>>> snap
=======
=======
>>>>>>> some more comments
                    let uu____31666 =
                      let uu____31667 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____31667]  in
                    FStar_TypeChecker_Env.close_guard env uu____31666 g1  in
<<<<<<< HEAD
>>>>>>> snap
=======
                    let uu____31713 =
                      let uu____31714 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____31714]  in
                    FStar_TypeChecker_Env.close_guard env uu____31713 g1  in
>>>>>>> cp debugging an issue
=======
>>>>>>> some more comments
=======
                    let uu____30124 =
                      let uu____30125 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____30125]  in
                    FStar_TypeChecker_Env.close_guard env uu____30124 g1  in
>>>>>>> snap
=======
                    let uu____31711 =
                      let uu____31712 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____31712]  in
                    FStar_TypeChecker_Env.close_guard env uu____31711 g1  in
>>>>>>> snap
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____30846 = subtype_nosmt env t1 t2  in
        match uu____30846 with
=======
        let uu____31841 = subtype_nosmt env t1 t2  in
        match uu____31841 with
>>>>>>> snap
=======
        let uu____30140 = subtype_nosmt env t1 t2  in
        match uu____30140 with
>>>>>>> snap
=======
        let uu____31841 = subtype_nosmt env t1 t2  in
        match uu____31841 with
>>>>>>> snap
=======
        let uu____31709 = subtype_nosmt env t1 t2  in
        match uu____31709 with
>>>>>>> snap
=======
        let uu____31633 = subtype_nosmt env t1 t2  in
        match uu____31633 with
>>>>>>> snap
=======
        let uu____31708 = subtype_nosmt env t1 t2  in
        match uu____31708 with
>>>>>>> snap
=======
        let uu____31755 = subtype_nosmt env t1 t2  in
        match uu____31755 with
>>>>>>> cp debugging an issue
=======
        let uu____31708 = subtype_nosmt env t1 t2  in
        match uu____31708 with
>>>>>>> some more comments
=======
        let uu____30166 = subtype_nosmt env t1 t2  in
        match uu____30166 with
>>>>>>> snap
=======
        let uu____31753 = subtype_nosmt env t1 t2  in
        match uu____31753 with
>>>>>>> snap
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  