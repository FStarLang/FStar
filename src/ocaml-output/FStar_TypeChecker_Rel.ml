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
                 ((let uu____6057 = FStar_Options.debug_any ()  in
                   if uu____6057
                   then
                     let uu____6060 =
                       FStar_Syntax_Print.ctx_uvar_to_string src  in
                     let uu____6062 =
                       FStar_Syntax_Print.binders_to_string ";;" pfx  in
                     let uu____6065 = FStar_Syntax_Print.term_to_string src'
                        in
                     let uu____6067 =
                       FStar_Syntax_Print.ctx_uvar_to_string tgt  in
                     FStar_Util.print4
                       "Restricting context of %s to %s with new uvar as %s (tgt : %s)\n\n"
                       uu____6060 uu____6062 uu____6065 uu____6067
                   else ());
                  FStar_Syntax_Unionfind.change
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
                 | uu____6183 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6184 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6248  ->
                  fun uu____6249  ->
                    match (uu____6248, uu____6249) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6352 =
                          let uu____6354 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6354
                           in
                        if uu____6352
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6388 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6388
                           then
                             let uu____6405 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6405)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6184 with | (isect,uu____6455) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____6491 'Auu____6492 .
    (FStar_Syntax_Syntax.bv * 'Auu____6491) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____6492) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6550  ->
              fun uu____6551  ->
                match (uu____6550, uu____6551) with
                | ((a,uu____6570),(b,uu____6572)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____6588 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____6588) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6619  ->
           match uu____6619 with
           | (y,uu____6626) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6636 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____6636) Prims.list ->
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
                   let uu____6798 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6798
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6831 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6883 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____6927 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____6948 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___22_6956  ->
    match uu___22_6956 with
    | MisMatch (d1,d2) ->
        let uu____6968 =
          let uu____6970 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____6972 =
            let uu____6974 =
              let uu____6976 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____6976 ")"  in
            Prims.op_Hat ") (" uu____6974  in
          Prims.op_Hat uu____6970 uu____6972  in
        Prims.op_Hat "MisMatch (" uu____6968
    | HeadMatch u ->
        let uu____6983 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____6983
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___23_6992  ->
    match uu___23_6992 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7009 -> HeadMatch false
  
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
          let uu____7031 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7031 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7042 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7066 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7076 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7103 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7103
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7104 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7105 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7106 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7119 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7133 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7157) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7163,uu____7164) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7206) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7231;
             FStar_Syntax_Syntax.index = uu____7232;
             FStar_Syntax_Syntax.sort = t2;_},uu____7234)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7242 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7243 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7244 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7259 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7266 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7286 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7286
  
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
           { FStar_Syntax_Syntax.blob = uu____7305;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7306;
             FStar_Syntax_Syntax.ltyp = uu____7307;
             FStar_Syntax_Syntax.rng = uu____7308;_},uu____7309)
            ->
            let uu____7320 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7320 t21
        | (uu____7321,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7322;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7323;
             FStar_Syntax_Syntax.ltyp = uu____7324;
             FStar_Syntax_Syntax.rng = uu____7325;_})
            ->
            let uu____7336 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7336
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7348 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7348
            then FullMatch
            else
              (let uu____7353 =
                 let uu____7362 =
                   let uu____7365 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7365  in
                 let uu____7366 =
                   let uu____7369 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7369  in
                 (uu____7362, uu____7366)  in
               MisMatch uu____7353)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7375),FStar_Syntax_Syntax.Tm_uinst (g,uu____7377)) ->
            let uu____7386 = head_matches env f g  in
            FStar_All.pipe_right uu____7386 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7387) -> HeadMatch true
        | (uu____7389,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7393 = FStar_Const.eq_const c d  in
            if uu____7393
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7403),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7405)) ->
            let uu____7438 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7438
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7448),FStar_Syntax_Syntax.Tm_refine (y,uu____7450)) ->
            let uu____7459 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7459 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____7461),uu____7462) ->
            let uu____7467 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____7467 head_match
        | (uu____7468,FStar_Syntax_Syntax.Tm_refine (x,uu____7470)) ->
            let uu____7475 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7475 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7476,FStar_Syntax_Syntax.Tm_type
           uu____7477) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____7479,FStar_Syntax_Syntax.Tm_arrow uu____7480) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____7511),FStar_Syntax_Syntax.Tm_app (head',uu____7513))
            ->
            let uu____7562 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____7562 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____7564),uu____7565) ->
            let uu____7590 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____7590 head_match
        | (uu____7591,FStar_Syntax_Syntax.Tm_app (head1,uu____7593)) ->
            let uu____7618 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____7618 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7619,FStar_Syntax_Syntax.Tm_let
           uu____7620) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____7648,FStar_Syntax_Syntax.Tm_match uu____7649) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7695,FStar_Syntax_Syntax.Tm_abs
           uu____7696) -> HeadMatch true
        | uu____7734 ->
            let uu____7739 =
              let uu____7748 = delta_depth_of_term env t11  in
              let uu____7751 = delta_depth_of_term env t21  in
              (uu____7748, uu____7751)  in
            MisMatch uu____7739
  
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
              let uu____7820 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____7820  in
            (let uu____7822 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7822
             then
               let uu____7827 = FStar_Syntax_Print.term_to_string t  in
               let uu____7829 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7827 uu____7829
             else ());
            (let uu____7834 =
               let uu____7835 = FStar_Syntax_Util.un_uinst head1  in
               uu____7835.FStar_Syntax_Syntax.n  in
             match uu____7834 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7841 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7841 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7855 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7855
                        then
                          let uu____7860 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7860
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7865 ->
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
                      let uu____7882 =
                        let uu____7884 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____7884 = FStar_Syntax_Util.Equal  in
                      if uu____7882
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____7891 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____7891
                          then
                            let uu____7896 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____7898 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____7896
                              uu____7898
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____7903 -> FStar_Pervasives_Native.None)
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
            (let uu____8055 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8055
             then
               let uu____8060 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8062 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8064 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8060
                 uu____8062 uu____8064
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8092 =
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
               match uu____8092 with
               | (t12,t22) -> aux retry (n_delta + Prims.int_one) t12 t22  in
             let reduce_both_and_try_again d r1 =
               let uu____8140 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8140 with
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
                  uu____8178),uu____8179)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8200 =
                      let uu____8209 = maybe_inline t11  in
                      let uu____8212 = maybe_inline t21  in
                      (uu____8209, uu____8212)  in
                    match uu____8200 with
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
                 (uu____8255,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8256))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8277 =
                      let uu____8286 = maybe_inline t11  in
                      let uu____8289 = maybe_inline t21  in
                      (uu____8286, uu____8289)  in
                    match uu____8277 with
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
             | MisMatch uu____8344 -> fail1 n_delta r t11 t21
             | uu____8353 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8368 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8368
           then
             let uu____8373 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8375 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8377 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8385 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8402 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8402
                    (fun uu____8437  ->
                       match uu____8437 with
                       | (t11,t21) ->
                           let uu____8445 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8447 =
                             let uu____8449 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____8449  in
                           Prims.op_Hat uu____8445 uu____8447))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8373 uu____8375 uu____8377 uu____8385
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____8466 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____8466 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___24_8481  ->
    match uu___24_8481 with
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
      let uu___1206_8530 = p  in
      let uu____8533 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8534 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1206_8530.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8533;
        FStar_TypeChecker_Common.relation =
          (uu___1206_8530.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8534;
        FStar_TypeChecker_Common.element =
          (uu___1206_8530.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1206_8530.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1206_8530.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1206_8530.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1206_8530.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1206_8530.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8549 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____8549
            (fun _8554  -> FStar_TypeChecker_Common.TProb _8554)
      | FStar_TypeChecker_Common.CProb uu____8555 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____8578 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____8578 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8586 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8586 with
           | (lh,lhs_args) ->
               let uu____8633 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8633 with
                | (rh,rhs_args) ->
                    let uu____8680 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8693,FStar_Syntax_Syntax.Tm_uvar uu____8694)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8783 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8810,uu____8811)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8826,FStar_Syntax_Syntax.Tm_uvar uu____8827)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8842,FStar_Syntax_Syntax.Tm_arrow uu____8843)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1257_8873 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1257_8873.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1257_8873.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1257_8873.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1257_8873.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1257_8873.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1257_8873.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1257_8873.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1257_8873.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1257_8873.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8876,FStar_Syntax_Syntax.Tm_type uu____8877)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1257_8893 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1257_8893.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1257_8893.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1257_8893.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1257_8893.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1257_8893.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1257_8893.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1257_8893.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1257_8893.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1257_8893.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____8896,FStar_Syntax_Syntax.Tm_uvar uu____8897)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1257_8913 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1257_8913.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1257_8913.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1257_8913.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1257_8913.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1257_8913.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1257_8913.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1257_8913.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1257_8913.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1257_8913.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____8916,FStar_Syntax_Syntax.Tm_uvar uu____8917)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8932,uu____8933)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8948,FStar_Syntax_Syntax.Tm_uvar uu____8949)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8964,uu____8965) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____8680 with
                     | (rank,tp1) ->
                         let uu____8978 =
                           FStar_All.pipe_right
                             (let uu___1277_8982 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1277_8982.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1277_8982.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1277_8982.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1277_8982.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1277_8982.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1277_8982.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1277_8982.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1277_8982.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1277_8982.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _8985  ->
                                FStar_TypeChecker_Common.TProb _8985)
                            in
                         (rank, uu____8978))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8989 =
            FStar_All.pipe_right
              (let uu___1281_8993 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1281_8993.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1281_8993.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1281_8993.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1281_8993.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1281_8993.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1281_8993.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1281_8993.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1281_8993.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1281_8993.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _8996  -> FStar_TypeChecker_Common.CProb _8996)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____8989)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9056 probs =
      match uu____9056 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9137 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____9158 = rank wl.tcenv hd1  in
               (match uu____9158 with
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
                      (let uu____9219 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9224 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9224)
                          in
                       if uu____9219
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
          let uu____9297 = FStar_Syntax_Util.head_and_args t  in
          match uu____9297 with
          | (hd1,uu____9316) ->
              let uu____9341 =
                let uu____9342 = FStar_Syntax_Subst.compress hd1  in
                uu____9342.FStar_Syntax_Syntax.n  in
              (match uu____9341 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9347) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9382  ->
                           match uu____9382 with
                           | (y,uu____9391) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9414  ->
                                       match uu____9414 with
                                       | (x,uu____9423) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9428 -> false)
           in
        let uu____9430 = rank tcenv p  in
        match uu____9430 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9439 -> true
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
    match projectee with | UDeferred _0 -> true | uu____9476 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9495 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9515 -> false
  
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
                        let uu____9577 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9577 with
                        | (k,uu____9585) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9598 -> false)))
            | uu____9600 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9652 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9660 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9660 = Prims.int_zero))
                           in
                        if uu____9652 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9681 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9689 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9689 = Prims.int_zero))
                      in
                   Prims.op_Negation uu____9681)
               in
            let uu____9693 = filter1 u12  in
            let uu____9696 = filter1 u22  in (uu____9693, uu____9696)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then UFailed "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9731 = filter_out_common_univs us1 us2  in
                   (match uu____9731 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____9791 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____9791 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9794 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          (let uu____9805 =
                             let uu____9807 =
                               FStar_Syntax_Print.univ_to_string u12  in
                             let uu____9809 =
                               FStar_Syntax_Print.univ_to_string u22  in
                             FStar_Util.format2
                               "Unable to unify universes: %s and %s"
                               uu____9807 uu____9809
                              in
                           UFailed uu____9805))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9835 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____9835 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9861 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____9861 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____9864 ->
                   let uu____9869 =
                     let uu____9871 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____9873 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format3
                       "Unable to unify universes: %s and %s (%s)" uu____9871
                       uu____9873 msg
                      in
                   UFailed uu____9869)
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9876,uu____9877) ->
              let uu____9879 =
                let uu____9881 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9883 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9881 uu____9883
                 in
              failwith uu____9879
          | (FStar_Syntax_Syntax.U_unknown ,uu____9886) ->
              let uu____9887 =
                let uu____9889 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9891 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9889 uu____9891
                 in
              failwith uu____9887
          | (uu____9894,FStar_Syntax_Syntax.U_bvar uu____9895) ->
              let uu____9897 =
                let uu____9899 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9901 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9899 uu____9901
                 in
              failwith uu____9897
          | (uu____9904,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9905 =
                let uu____9907 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9909 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9907 uu____9909
                 in
              failwith uu____9905
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9939 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____9939
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____9956 = occurs_univ v1 u3  in
              if uu____9956
              then
                let uu____9959 =
                  let uu____9961 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9963 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9961 uu____9963
                   in
                try_umax_components u11 u21 uu____9959
              else
                (let uu____9968 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9968)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____9980 = occurs_univ v1 u3  in
              if uu____9980
              then
                let uu____9983 =
                  let uu____9985 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9987 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9985 uu____9987
                   in
                try_umax_components u11 u21 uu____9983
              else
                (let uu____9992 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9992)
          | (FStar_Syntax_Syntax.U_max uu____9993,uu____9994) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10002 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10002
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10008,FStar_Syntax_Syntax.U_max uu____10009) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10017 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10017
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10023,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10025,FStar_Syntax_Syntax.U_name uu____10026) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10028) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10030) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10032,FStar_Syntax_Syntax.U_succ uu____10033) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10035,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10142 = bc1  in
      match uu____10142 with
      | (bs1,mk_cod1) ->
          let uu____10186 = bc2  in
          (match uu____10186 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10297 = aux xs ys  in
                     (match uu____10297 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10380 =
                       let uu____10387 = mk_cod1 xs  in ([], uu____10387)  in
                     let uu____10390 =
                       let uu____10397 = mk_cod2 ys  in ([], uu____10397)  in
                     (uu____10380, uu____10390)
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
                  let uu____10466 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10466 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____10469 =
                    let uu____10470 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____10470 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____10469
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____10475 = has_type_guard t1 t2  in (uu____10475, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____10476 = has_type_guard t2 t1  in (uu____10476, wl)
  
let is_flex_pat :
  'Auu____10486 'Auu____10487 'Auu____10488 .
    ('Auu____10486 * 'Auu____10487 * 'Auu____10488 Prims.list) -> Prims.bool
  =
  fun uu___25_10502  ->
    match uu___25_10502 with
    | (uu____10511,uu____10512,[]) -> true
    | uu____10516 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____10549 = f  in
      match uu____10549 with
      | (uu____10556,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____10557;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10558;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____10561;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____10562;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____10563;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____10564;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10634  ->
                 match uu____10634 with
                 | (y,uu____10643) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____10797 =
                  let uu____10812 =
                    let uu____10815 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____10815  in
                  ((FStar_List.rev pat_binders), uu____10812)  in
                FStar_Pervasives_Native.Some uu____10797
            | (uu____10848,[]) ->
                let uu____10879 =
                  let uu____10894 =
                    let uu____10897 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____10897  in
                  ((FStar_List.rev pat_binders), uu____10894)  in
                FStar_Pervasives_Native.Some uu____10879
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____10988 =
                  let uu____10989 = FStar_Syntax_Subst.compress a  in
                  uu____10989.FStar_Syntax_Syntax.n  in
                (match uu____10988 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11009 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11009
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1605_11039 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1605_11039.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1605_11039.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____11043 =
                            let uu____11044 =
                              let uu____11051 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11051)  in
                            FStar_Syntax_Syntax.NT uu____11044  in
                          [uu____11043]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___1611_11067 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1611_11067.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1611_11067.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11068 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11108 =
                  let uu____11123 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11123  in
                (match uu____11108 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11198 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11231 ->
               let uu____11232 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11232 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____11554 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____11554
       then
         let uu____11559 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11559
       else ());
      (let uu____11564 = next_prob probs  in
       match uu____11564 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___1636_11591 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___1636_11591.wl_deferred);
               ctr = (uu___1636_11591.ctr);
               defer_ok = (uu___1636_11591.defer_ok);
               smt_ok = (uu___1636_11591.smt_ok);
               umax_heuristic_ok = (uu___1636_11591.umax_heuristic_ok);
               tcenv = (uu___1636_11591.tcenv);
               wl_implicits = (uu___1636_11591.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11600 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____11600
                 then
                   let uu____11603 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____11603
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
                           (let uu___1648_11615 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1648_11615.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1648_11615.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1648_11615.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1648_11615.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1648_11615.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1648_11615.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1648_11615.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1648_11615.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1648_11615.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____11641 ->
                let uu____11652 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11723  ->
                          match uu____11723 with
                          | (c,uu____11734,uu____11735) -> c < probs.ctr))
                   in
                (match uu____11652 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11790 =
                            let uu____11795 =
                              FStar_List.map
                                (fun uu____11813  ->
                                   match uu____11813 with
                                   | (uu____11827,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____11795, (probs.wl_implicits))  in
                          Success uu____11790
                      | uu____11835 ->
                          let uu____11846 =
                            let uu___1666_11847 = probs  in
                            let uu____11848 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____11871  ->
                                      match uu____11871 with
                                      | (uu____11880,uu____11881,y) -> y))
                               in
                            {
                              attempting = uu____11848;
                              wl_deferred = rest;
                              ctr = (uu___1666_11847.ctr);
                              defer_ok = (uu___1666_11847.defer_ok);
                              smt_ok = (uu___1666_11847.smt_ok);
                              umax_heuristic_ok =
                                (uu___1666_11847.umax_heuristic_ok);
                              tcenv = (uu___1666_11847.tcenv);
                              wl_implicits = (uu___1666_11847.wl_implicits)
                            }  in
                          solve env uu____11846))))

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
            let uu____11892 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____11892 with
            | USolved wl1 ->
                let uu____11894 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____11894
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
                  let uu____11948 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____11948 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____11951 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____11964;
                  FStar_Syntax_Syntax.vars = uu____11965;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____11968;
                  FStar_Syntax_Syntax.vars = uu____11969;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____11982,uu____11983) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____11991,FStar_Syntax_Syntax.Tm_uinst uu____11992) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12000 -> USolved wl

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
            ((let uu____12012 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12012
              then
                let uu____12017 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12017 msg
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
               let uu____12109 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12109 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12164 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12164
                then
                  let uu____12169 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12171 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12169 uu____12171
                else ());
               (let uu____12176 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12176 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12222 = eq_prob t1 t2 wl2  in
                         (match uu____12222 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12243 ->
                         let uu____12252 = eq_prob t1 t2 wl2  in
                         (match uu____12252 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____12302 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____12317 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____12318 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____12317, uu____12318)
                           | FStar_Pervasives_Native.None  ->
                               let uu____12323 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____12324 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____12323, uu____12324)
                            in
                         (match uu____12302 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12355 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____12355 with
                                | (t1_hd,t1_args) ->
                                    let uu____12400 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____12400 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12466 =
                                              let uu____12473 =
                                                let uu____12484 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____12484 :: t1_args  in
                                              let uu____12501 =
                                                let uu____12510 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____12510 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____12559  ->
                                                   fun uu____12560  ->
                                                     fun uu____12561  ->
                                                       match (uu____12559,
                                                               uu____12560,
                                                               uu____12561)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____12611),
                                                          (a2,uu____12613))
                                                           ->
                                                           let uu____12650 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____12650
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12473
                                                uu____12501
                                               in
                                            match uu____12466 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1820_12676 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___1820_12676.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1820_12676.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1820_12676.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12688 =
                                                  solve env1 wl'  in
                                                (match uu____12688 with
                                                 | Success (uu____12691,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___1829_12695
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___1829_12695.attempting);
                                                            wl_deferred =
                                                              (uu___1829_12695.wl_deferred);
                                                            ctr =
                                                              (uu___1829_12695.ctr);
                                                            defer_ok =
                                                              (uu___1829_12695.defer_ok);
                                                            smt_ok =
                                                              (uu___1829_12695.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___1829_12695.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___1829_12695.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____12696 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____12729 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____12729 with
                                | (t1_base,p1_opt) ->
                                    let uu____12765 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____12765 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____12864 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____12864
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
                                               let uu____12917 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____12917
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
                                               let uu____12949 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____12949
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
                                               let uu____12981 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____12981
                                           | uu____12984 -> t_base  in
                                         let uu____13001 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13001 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13015 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13015, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13022 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13022 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13058 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13058 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13094 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13094
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
                              let uu____13118 = combine t11 t21 wl2  in
                              (match uu____13118 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13151 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13151
                                     then
                                       let uu____13156 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13156
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13198 ts1 =
               match uu____13198 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13261 = pairwise out t wl2  in
                        (match uu____13261 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____13297 =
               let uu____13308 = FStar_List.hd ts  in (uu____13308, [], wl1)
                in
             let uu____13317 = FStar_List.tl ts  in
             aux uu____13297 uu____13317  in
           let uu____13324 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____13324 with
           | (this_flex,this_rigid) ->
               let uu____13350 =
                 let uu____13351 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____13351.FStar_Syntax_Syntax.n  in
               (match uu____13350 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____13376 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____13376
                    then
                      let uu____13379 = destruct_flex_t this_flex wl  in
                      (match uu____13379 with
                       | (flex,wl1) ->
                           let uu____13386 = quasi_pattern env flex  in
                           (match uu____13386 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____13405 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____13405
                                  then
                                    let uu____13410 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13410
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13417 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___1931_13420 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___1931_13420.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___1931_13420.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___1931_13420.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___1931_13420.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___1931_13420.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___1931_13420.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___1931_13420.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___1931_13420.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___1931_13420.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____13417)
                | uu____13421 ->
                    ((let uu____13423 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13423
                      then
                        let uu____13428 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13428
                      else ());
                     (let uu____13433 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____13433 with
                      | (u,_args) ->
                          let uu____13476 =
                            let uu____13477 = FStar_Syntax_Subst.compress u
                               in
                            uu____13477.FStar_Syntax_Syntax.n  in
                          (match uu____13476 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____13505 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____13505 with
                                 | (u',uu____13524) ->
                                     let uu____13549 =
                                       let uu____13550 = whnf env u'  in
                                       uu____13550.FStar_Syntax_Syntax.n  in
                                     (match uu____13549 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13572 -> false)
                                  in
                               let uu____13574 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___26_13597  ->
                                         match uu___26_13597 with
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
                                              | uu____13611 -> false)
                                         | uu____13615 -> false))
                                  in
                               (match uu____13574 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____13630 = whnf env this_rigid
                                         in
                                      let uu____13631 =
                                        FStar_List.collect
                                          (fun uu___27_13637  ->
                                             match uu___27_13637 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13643 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____13643]
                                             | uu____13647 -> [])
                                          bounds_probs
                                         in
                                      uu____13630 :: uu____13631  in
                                    let uu____13648 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____13648 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____13681 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____13696 =
                                               let uu____13697 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____13697.FStar_Syntax_Syntax.n
                                                in
                                             match uu____13696 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13709 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13709)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13720 -> bound  in
                                           let uu____13721 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____13721)  in
                                         (match uu____13681 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13756 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____13756
                                                then
                                                  let wl'1 =
                                                    let uu___1991_13762 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___1991_13762.wl_deferred);
                                                      ctr =
                                                        (uu___1991_13762.ctr);
                                                      defer_ok =
                                                        (uu___1991_13762.defer_ok);
                                                      smt_ok =
                                                        (uu___1991_13762.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___1991_13762.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___1991_13762.tcenv);
                                                      wl_implicits =
                                                        (uu___1991_13762.wl_implicits)
                                                    }  in
                                                  let uu____13763 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13763
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13769 =
                                                  solve_t env eq_prob
                                                    (let uu___1996_13771 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___1996_13771.wl_deferred);
                                                       ctr =
                                                         (uu___1996_13771.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___1996_13771.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___1996_13771.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___1996_13771.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____13769 with
                                                | Success (uu____13773,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2002_13776 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2002_13776.wl_deferred);
                                                        ctr =
                                                          (uu___2002_13776.ctr);
                                                        defer_ok =
                                                          (uu___2002_13776.defer_ok);
                                                        smt_ok =
                                                          (uu___2002_13776.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2002_13776.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2002_13776.tcenv);
                                                        wl_implicits =
                                                          (uu___2002_13776.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2005_13778 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2005_13778.attempting);
                                                        wl_deferred =
                                                          (uu___2005_13778.wl_deferred);
                                                        ctr =
                                                          (uu___2005_13778.ctr);
                                                        defer_ok =
                                                          (uu___2005_13778.defer_ok);
                                                        smt_ok =
                                                          (uu___2005_13778.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2005_13778.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2005_13778.tcenv);
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
                                                    let uu____13794 =
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
                                                    ((let uu____13808 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____13808
                                                      then
                                                        let uu____13813 =
                                                          let uu____13815 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____13815
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13813
                                                      else ());
                                                     (let uu____13828 =
                                                        let uu____13843 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____13843)
                                                         in
                                                      match uu____13828 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____13865))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13891 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____13891
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
                                                                  let uu____13911
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____13911))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13936 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____13936
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
                                                                    let uu____13956
                                                                    =
                                                                    let uu____13961
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____13961
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____13956
                                                                    [] wl2
                                                                     in
                                                                  let uu____13967
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____13967))))
                                                      | uu____13968 ->
                                                          giveup env
                                                            (Prims.op_Hat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____13984 when flip ->
                               let uu____13985 =
                                 let uu____13987 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____13989 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____13987 uu____13989
                                  in
                               failwith uu____13985
                           | uu____13992 ->
                               let uu____13993 =
                                 let uu____13995 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____13997 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____13995 uu____13997
                                  in
                               failwith uu____13993)))))

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
                      (fun uu____14033  ->
                         match uu____14033 with
                         | (x,i) ->
                             let uu____14052 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14052, i)) bs_lhs
                     in
                  let uu____14055 = lhs  in
                  match uu____14055 with
                  | (uu____14056,u_lhs,uu____14058) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14155 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14165 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14165, univ)
                             in
                          match uu____14155 with
                          | (k,univ) ->
                              let uu____14172 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14172 with
                               | (uu____14189,u,wl3) ->
                                   let uu____14192 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14192, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14218 =
                              let uu____14231 =
                                let uu____14242 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14242 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____14293  ->
                                   fun uu____14294  ->
                                     match (uu____14293, uu____14294) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____14395 =
                                           let uu____14402 =
                                             let uu____14405 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____14405
                                              in
                                           copy_uvar u_lhs [] uu____14402 wl2
                                            in
                                         (match uu____14395 with
                                          | (uu____14434,t_a,wl3) ->
                                              let uu____14437 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____14437 with
                                               | (uu____14456,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14231
                                ([], wl1)
                               in
                            (match uu____14218 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2115_14512 = ct  in
                                   let uu____14513 =
                                     let uu____14516 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14516
                                      in
                                   let uu____14531 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2115_14512.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2115_14512.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14513;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14531;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2115_14512.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2118_14549 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2118_14549.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2118_14549.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14552 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____14552 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14614 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14614 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____14625 =
                                          let uu____14630 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____14630)  in
                                        TERM uu____14625  in
                                      let uu____14631 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____14631 with
                                       | (sub_prob,wl3) ->
                                           let uu____14645 =
                                             let uu____14646 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____14646
                                              in
                                           solve env uu____14645))
                             | (x,imp)::formals2 ->
                                 let uu____14668 =
                                   let uu____14675 =
                                     let uu____14678 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____14678
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14675 wl1
                                    in
                                 (match uu____14668 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____14699 =
                                          let uu____14702 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14702
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14699 u_x
                                         in
                                      let uu____14703 =
                                        let uu____14706 =
                                          let uu____14709 =
                                            let uu____14710 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____14710, imp)  in
                                          [uu____14709]  in
                                        FStar_List.append bs_terms
                                          uu____14706
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14703 formals2 wl2)
                              in
                           let uu____14737 = occurs_check u_lhs arrow1  in
                           (match uu____14737 with
                            | (uu____14750,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14766 =
                                    let uu____14768 = FStar_Option.get msg
                                       in
                                    Prims.op_Hat "occurs-check failed: "
                                      uu____14768
                                     in
                                  giveup_or_defer env orig wl uu____14766
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
              (let uu____14801 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____14801
               then
                 let uu____14806 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____14809 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14806 (rel_to_string (p_rel orig)) uu____14809
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____14936 = rhs wl1 scope env1 subst1  in
                     (match uu____14936 with
                      | (rhs_prob,wl2) ->
                          ((let uu____14957 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____14957
                            then
                              let uu____14962 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____14962
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15040 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15040 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2187_15042 = hd1  in
                       let uu____15043 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2187_15042.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2187_15042.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15043
                       }  in
                     let hd21 =
                       let uu___2190_15047 = hd2  in
                       let uu____15048 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2190_15047.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2190_15047.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15048
                       }  in
                     let uu____15051 =
                       let uu____15056 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15056
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15051 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____15077 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst1
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15077
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15084 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____15084 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15151 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15151
                                  in
                               ((let uu____15169 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15169
                                 then
                                   let uu____15174 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15176 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15174
                                     uu____15176
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____15209 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15245 = aux wl [] env [] bs1 bs2  in
               match uu____15245 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15300 = attempt sub_probs wl2  in
                   solve env uu____15300)

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
            let uu___2225_15321 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2225_15321.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2225_15321.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15334 = try_solve env wl'  in
          match uu____15334 with
          | Success (uu____15335,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2234_15339 = wl  in
                  {
                    attempting = (uu___2234_15339.attempting);
                    wl_deferred = (uu___2234_15339.wl_deferred);
                    ctr = (uu___2234_15339.ctr);
                    defer_ok = (uu___2234_15339.defer_ok);
                    smt_ok = (uu___2234_15339.smt_ok);
                    umax_heuristic_ok = (uu___2234_15339.umax_heuristic_ok);
                    tcenv = (uu___2234_15339.tcenv);
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
        (let uu____15351 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15351 wl)

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
              let uu____15365 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15365 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15399 = lhs1  in
              match uu____15399 with
              | (uu____15402,ctx_u,uu____15404) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15412 ->
                        let uu____15413 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15413 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15462 = quasi_pattern env1 lhs1  in
              match uu____15462 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15496) ->
                  let uu____15501 = lhs1  in
                  (match uu____15501 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15516 = occurs_check ctx_u rhs1  in
                       (match uu____15516 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15567 =
                                let uu____15575 =
                                  let uu____15577 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15577
                                   in
                                FStar_Util.Inl uu____15575  in
                              (uu____15567, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15605 =
                                 let uu____15607 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15607  in
                               if uu____15605
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15634 =
                                    let uu____15642 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15642  in
                                  let uu____15648 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____15634, uu____15648)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____15692 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____15692 with
              | (rhs_hd,args) ->
                  let uu____15735 = FStar_Util.prefix args  in
                  (match uu____15735 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15807 = lhs1  in
                       (match uu____15807 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____15811 =
                              let uu____15822 =
                                let uu____15829 =
                                  let uu____15832 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____15832
                                   in
                                copy_uvar u_lhs [] uu____15829 wl1  in
                              match uu____15822 with
                              | (uu____15859,t_last_arg,wl2) ->
                                  let uu____15862 =
                                    let uu____15869 =
                                      let uu____15870 =
                                        let uu____15879 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____15879]  in
                                      FStar_List.append bs_lhs uu____15870
                                       in
                                    copy_uvar u_lhs uu____15869 t_res_lhs wl2
                                     in
                                  (match uu____15862 with
                                   | (uu____15914,lhs',wl3) ->
                                       let uu____15917 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____15917 with
                                        | (uu____15934,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____15811 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____15955 =
                                     let uu____15956 =
                                       let uu____15961 =
                                         let uu____15962 =
                                           let uu____15965 =
                                             let uu____15970 =
                                               let uu____15971 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____15971]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____15970
                                              in
                                           uu____15965
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____15962
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____15961)  in
                                     TERM uu____15956  in
                                   [uu____15955]  in
                                 let uu____15996 =
                                   let uu____16003 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____16003 with
                                   | (p1,wl3) ->
                                       let uu____16023 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____16023 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____15996 with
                                  | (sub_probs,wl3) ->
                                      let uu____16055 =
                                        let uu____16056 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____16056  in
                                      solve env1 uu____16055))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16090 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16090 with
                | (uu____16108,args) ->
                    (match args with | [] -> false | uu____16144 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16163 =
                  let uu____16164 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16164.FStar_Syntax_Syntax.n  in
                match uu____16163 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16168 -> true
                | uu____16184 -> false  in
              let uu____16186 = quasi_pattern env1 lhs1  in
              match uu____16186 with
              | FStar_Pervasives_Native.None  ->
                  let uu____16197 =
                    let uu____16199 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                      uu____16199
                     in
                  giveup_or_defer env1 orig1 wl1 uu____16197
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16208 = is_app rhs1  in
                  if uu____16208
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____16213 = is_arrow rhs1  in
                     if uu____16213
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____16218 =
                          let uu____16220 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heuristic cannot solve %s; rhs not an app or arrow"
                            uu____16220
                           in
                        giveup_or_defer env1 orig1 wl1 uu____16218))
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
                let uu____16231 = lhs  in
                (match uu____16231 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16235 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16235 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16253 =
                              let uu____16257 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16257
                               in
                            FStar_All.pipe_right uu____16253
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16278 = occurs_check ctx_uv rhs1  in
                          (match uu____16278 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16307 =
                                   let uu____16309 = FStar_Option.get msg  in
                                   Prims.op_Hat "occurs-check failed: "
                                     uu____16309
                                    in
                                 giveup_or_defer env orig wl uu____16307
                               else
                                 (let uu____16315 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____16315
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    ((let uu____16322 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          FStar_Options.Extreme
                                         in
                                      if uu____16322
                                      then
                                        let uu____16326 =
                                          flex_t_to_string lhs  in
                                        let uu____16328 =
                                          FStar_Syntax_Print.term_to_string
                                            rhs1
                                           in
                                        let uu____16330 =
                                          FStar_List.fold_left
                                            (fun s  ->
                                               fun uv  ->
                                                 let uu____16339 =
                                                   let uu____16341 =
                                                     FStar_Syntax_Print.ctx_uvar_to_string
                                                       uv
                                                      in
                                                   Prims.op_Hat ";;;;"
                                                     uu____16341
                                                    in
                                                 Prims.op_Hat s uu____16339)
                                            "" uvars1
                                           in
                                        let uu____16345 =
                                          names_to_string1 fvs1  in
                                        let uu____16347 =
                                          names_to_string1 fvs2  in
                                        FStar_Util.print5
                                          "About to restrict context uvars, here is the info:\nL.H.S.: %s\nR.H.S.: %s\nuvars from occurs_check: %s\nfvs1: %s\nfvs2: %s\n"
                                          uu____16326 uu____16328 uu____16330
                                          uu____16345 uu____16347
                                      else ());
                                     (let wl1 =
                                        restrict_all_uvars ctx_uv uvars1 wl
                                         in
                                      let uu____16353 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None sol
                                          wl1
                                         in
                                      solve env uu____16353))
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____16357 =
                                         let uu____16359 =
                                           names_to_string1 fvs2  in
                                         let uu____16361 =
                                           names_to_string1 fvs1  in
                                         let uu____16363 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____16359 uu____16361
                                           uu____16363
                                          in
                                       giveup_or_defer env orig wl
                                         uu____16357)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16375 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____16382 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16382 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16408 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16408
                             | (FStar_Util.Inl msg,uu____16410) ->
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
                  (let uu____16455 =
                     let uu____16472 = quasi_pattern env lhs  in
                     let uu____16479 = quasi_pattern env rhs  in
                     (uu____16472, uu____16479)  in
                   match uu____16455 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16522 = lhs  in
                       (match uu____16522 with
                        | ({ FStar_Syntax_Syntax.n = uu____16523;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____16525;_},u_lhs,uu____16527)
                            ->
                            let uu____16530 = rhs  in
                            (match uu____16530 with
                             | (uu____16531,u_rhs,uu____16533) ->
                                 let uu____16534 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16534
                                 then
                                   let uu____16541 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16541
                                 else
                                   (let uu____16544 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16544 with
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
                                        let uu____16576 =
                                          let uu____16583 =
                                            let uu____16586 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16586
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16583
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____16576 with
                                         | (uu____16598,w,wl1) ->
                                             let w_app =
                                               let uu____16604 =
                                                 let uu____16609 =
                                                   FStar_List.map
                                                     (fun uu____16620  ->
                                                        match uu____16620
                                                        with
                                                        | (z,uu____16628) ->
                                                            let uu____16633 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____16633) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____16609
                                                  in
                                               uu____16604
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16635 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16635
                                               then
                                                 let uu____16640 =
                                                   let uu____16644 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16646 =
                                                     let uu____16650 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____16652 =
                                                       let uu____16656 =
                                                         term_to_string w  in
                                                       let uu____16658 =
                                                         let uu____16662 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____16671 =
                                                           let uu____16675 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____16684 =
                                                             let uu____16688
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____16688]
                                                              in
                                                           uu____16675 ::
                                                             uu____16684
                                                            in
                                                         uu____16662 ::
                                                           uu____16671
                                                          in
                                                       uu____16656 ::
                                                         uu____16658
                                                        in
                                                     uu____16650 ::
                                                       uu____16652
                                                      in
                                                   uu____16644 :: uu____16646
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16640
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____16705 =
                                                     let uu____16710 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____16710)  in
                                                   TERM uu____16705  in
                                                 let uu____16711 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____16711
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____16719 =
                                                        let uu____16724 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____16724)
                                                         in
                                                      TERM uu____16719  in
                                                    [s1; s2])
                                                  in
                                               let uu____16725 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____16725))))))
                   | uu____16726 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____16797 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____16797
            then
              let uu____16802 = FStar_Syntax_Print.term_to_string t1  in
              let uu____16804 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____16806 = FStar_Syntax_Print.term_to_string t2  in
              let uu____16808 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____16802 uu____16804 uu____16806 uu____16808
            else ());
           (let uu____16819 = FStar_Syntax_Util.head_and_args t1  in
            match uu____16819 with
            | (head1,args1) ->
                let uu____16862 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____16862 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____16932 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____16932 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              k false (defer "universe constraints" orig wl3))
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____16958 =
                         let uu____16960 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____16962 = args_to_string args1  in
                         let uu____16966 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____16968 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____16960 uu____16962 uu____16966 uu____16968
                          in
                       giveup env1 uu____16958 orig
                     else
                       (let uu____16975 =
                          (nargs = Prims.int_zero) ||
                            (let uu____16980 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____16980 = FStar_Syntax_Util.Equal)
                           in
                        if uu____16975
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2487_16984 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2487_16984.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2487_16984.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2487_16984.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2487_16984.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2487_16984.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2487_16984.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2487_16984.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2487_16984.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____16994 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____16994
                                    else solve env1 wl2))
                        else
                          (let uu____16999 = base_and_refinement env1 t1  in
                           match uu____16999 with
                           | (base1,refinement1) ->
                               let uu____17024 = base_and_refinement env1 t2
                                  in
                               (match uu____17024 with
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
                                           let uu____17189 =
                                             FStar_List.fold_right
                                               (fun uu____17229  ->
                                                  fun uu____17230  ->
                                                    match (uu____17229,
                                                            uu____17230)
                                                    with
                                                    | (((a1,uu____17282),
                                                        (a2,uu____17284)),
                                                       (probs,wl3)) ->
                                                        let uu____17333 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17333
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17189 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17376 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17376
                                                 then
                                                   let uu____17381 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17381
                                                 else ());
                                                (let uu____17387 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17387
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
                                                    (let uu____17414 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17414 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17430 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17430
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17438 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17438))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____17462 =
                                                    mk_sub_probs wl3  in
                                                  match uu____17462 with
                                                  | (subprobs,wl4) ->
                                                      let wl5 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          [] wl4
                                                         in
                                                      let uu____17476 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____17476)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17502 =
                                           match uu____17502 with
                                           | (prob,reason) ->
                                               ((let uu____17513 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17513
                                                 then
                                                   let uu____17518 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____17520 =
                                                     prob_to_string env2 prob
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____17518 uu____17520
                                                     reason
                                                 else ());
                                                (let uu____17525 =
                                                   let uu____17534 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____17537 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____17534, uu____17537)
                                                    in
                                                 match uu____17525 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____17550 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____17550 with
                                                      | (head1',uu____17568)
                                                          ->
                                                          let uu____17593 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____17593
                                                           with
                                                           | (head2',uu____17611)
                                                               ->
                                                               let uu____17636
                                                                 =
                                                                 let uu____17641
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____17642
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____17641,
                                                                   uu____17642)
                                                                  in
                                                               (match uu____17636
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____17644
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17644
                                                                    then
                                                                    let uu____17649
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____17651
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____17653
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____17655
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17649
                                                                    uu____17651
                                                                    uu____17653
                                                                    uu____17655
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____17660
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2573_17668
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2573_17668.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2573_17668.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2573_17668.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2573_17668.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2573_17668.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2573_17668.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2573_17668.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2573_17668.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____17670
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17670
                                                                    then
                                                                    let uu____17675
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____17675
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____17680 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____17692 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____17692 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____17700 =
                                             let uu____17701 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____17701.FStar_Syntax_Syntax.n
                                              in
                                           match uu____17700 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____17706 -> false  in
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
                                          | uu____17709 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____17712 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2593_17748 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2593_17748.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2593_17748.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2593_17748.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2593_17748.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2593_17748.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2593_17748.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2593_17748.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2593_17748.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____17824 = destruct_flex_t scrutinee wl1  in
             match uu____17824 with
             | ((_t,uv,_args),wl2) ->
                 let uu____17835 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____17835 with
                  | (xs,pat_term,uu____17851,uu____17852) ->
                      let uu____17857 =
                        FStar_List.fold_left
                          (fun uu____17880  ->
                             fun x  ->
                               match uu____17880 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____17901 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____17901 with
                                    | (uu____17920,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____17857 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____17941 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____17941 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2633_17958 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2633_17958.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2633_17958.umax_heuristic_ok);
                                    tcenv = (uu___2633_17958.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____17970 = solve env1 wl'  in
                                (match uu____17970 with
                                 | Success (uu____17973,imps) ->
                                     let wl'1 =
                                       let uu___2641_17976 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2641_17976.wl_deferred);
                                         ctr = (uu___2641_17976.ctr);
                                         defer_ok =
                                           (uu___2641_17976.defer_ok);
                                         smt_ok = (uu___2641_17976.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2641_17976.umax_heuristic_ok);
                                         tcenv = (uu___2641_17976.tcenv);
                                         wl_implicits =
                                           (uu___2641_17976.wl_implicits)
                                       }  in
                                     let uu____17977 = solve env1 wl'1  in
                                     (match uu____17977 with
                                      | Success (uu____17980,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2649_17984 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2649_17984.attempting);
                                                 wl_deferred =
                                                   (uu___2649_17984.wl_deferred);
                                                 ctr = (uu___2649_17984.ctr);
                                                 defer_ok =
                                                   (uu___2649_17984.defer_ok);
                                                 smt_ok =
                                                   (uu___2649_17984.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2649_17984.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2649_17984.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____17985 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____17992 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18015 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18015
                 then
                   let uu____18020 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18022 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18020 uu____18022
                 else ());
                (let uu____18027 =
                   let uu____18048 =
                     let uu____18057 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18057)  in
                   let uu____18064 =
                     let uu____18073 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18073)  in
                   (uu____18048, uu____18064)  in
                 match uu____18027 with
                 | ((uu____18103,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18106;
                                   FStar_Syntax_Syntax.vars = uu____18107;_}),
                    (s,t)) ->
                     let uu____18178 =
                       let uu____18180 = is_flex scrutinee  in
                       Prims.op_Negation uu____18180  in
                     if uu____18178
                     then
                       ((let uu____18191 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18191
                         then
                           let uu____18196 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18196
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18215 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18215
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18230 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18230
                           then
                             let uu____18235 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18237 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18235 uu____18237
                           else ());
                          (let pat_discriminates uu___28_18262 =
                             match uu___28_18262 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18278;
                                  FStar_Syntax_Syntax.p = uu____18279;_},FStar_Pervasives_Native.None
                                ,uu____18280) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18294;
                                  FStar_Syntax_Syntax.p = uu____18295;_},FStar_Pervasives_Native.None
                                ,uu____18296) -> true
                             | uu____18323 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18426 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18426 with
                                       | (uu____18428,uu____18429,t') ->
                                           let uu____18447 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18447 with
                                            | (FullMatch ,uu____18459) ->
                                                true
                                            | (HeadMatch
                                               uu____18473,uu____18474) ->
                                                true
                                            | uu____18489 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18526 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18526
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18537 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18537 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18625,uu____18626) ->
                                       branches1
                                   | uu____18771 -> branches  in
                                 let uu____18826 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____18835 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____18835 with
                                        | (p,uu____18839,uu____18840) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _18869  -> FStar_Util.Inr _18869)
                                   uu____18826))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____18899 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____18899 with
                                | (p,uu____18908,e) ->
                                    ((let uu____18927 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____18927
                                      then
                                        let uu____18932 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____18934 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____18932 uu____18934
                                      else ());
                                     (let uu____18939 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _18954  -> FStar_Util.Inr _18954)
                                        uu____18939)))))
                 | ((s,t),(uu____18957,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____18960;
                                         FStar_Syntax_Syntax.vars =
                                           uu____18961;_}))
                     ->
                     let uu____19030 =
                       let uu____19032 = is_flex scrutinee  in
                       Prims.op_Negation uu____19032  in
                     if uu____19030
                     then
                       ((let uu____19043 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19043
                         then
                           let uu____19048 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19048
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19067 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19067
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19082 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19082
                           then
                             let uu____19087 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19089 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19087 uu____19089
                           else ());
                          (let pat_discriminates uu___28_19114 =
                             match uu___28_19114 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19130;
                                  FStar_Syntax_Syntax.p = uu____19131;_},FStar_Pervasives_Native.None
                                ,uu____19132) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19146;
                                  FStar_Syntax_Syntax.p = uu____19147;_},FStar_Pervasives_Native.None
                                ,uu____19148) -> true
                             | uu____19175 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19278 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19278 with
                                       | (uu____19280,uu____19281,t') ->
                                           let uu____19299 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19299 with
                                            | (FullMatch ,uu____19311) ->
                                                true
                                            | (HeadMatch
                                               uu____19325,uu____19326) ->
                                                true
                                            | uu____19341 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19378 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19378
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19389 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19389 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19477,uu____19478) ->
                                       branches1
                                   | uu____19623 -> branches  in
                                 let uu____19678 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19687 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19687 with
                                        | (p,uu____19691,uu____19692) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19721  -> FStar_Util.Inr _19721)
                                   uu____19678))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19751 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19751 with
                                | (p,uu____19760,e) ->
                                    ((let uu____19779 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19779
                                      then
                                        let uu____19784 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19786 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19784 uu____19786
                                      else ());
                                     (let uu____19791 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19806  -> FStar_Util.Inr _19806)
                                        uu____19791)))))
                 | uu____19807 ->
                     ((let uu____19829 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____19829
                       then
                         let uu____19834 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____19836 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____19834 uu____19836
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____19882 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____19882
            then
              let uu____19887 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____19889 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____19891 = FStar_Syntax_Print.term_to_string t1  in
              let uu____19893 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____19887 uu____19889 uu____19891 uu____19893
            else ());
           (let uu____19898 = head_matches_delta env1 wl1 t1 t2  in
            match uu____19898 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____19929,uu____19930) ->
                     let rec may_relate head3 =
                       let uu____19958 =
                         let uu____19959 = FStar_Syntax_Subst.compress head3
                            in
                         uu____19959.FStar_Syntax_Syntax.n  in
                       match uu____19958 with
                       | FStar_Syntax_Syntax.Tm_name uu____19963 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____19965 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____19990 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____19990 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____19992 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____19995
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____19996 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____19999,uu____20000) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20042) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20048) ->
                           may_relate t
                       | uu____20053 -> false  in
                     let uu____20055 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20055 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20076 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20076
                          then
                            let uu____20079 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20079 with
                             | (guard,wl2) ->
                                 let uu____20086 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20086)
                          else
                            (let uu____20089 =
                               let uu____20091 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____20093 =
                                 let uu____20095 =
                                   let uu____20099 =
                                     delta_depth_of_term env1 head1  in
                                   FStar_Util.bind_opt uu____20099
                                     (fun x  ->
                                        let uu____20106 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____20106)
                                    in
                                 FStar_Util.dflt "" uu____20095  in
                               let uu____20111 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               let uu____20113 =
                                 let uu____20115 =
                                   let uu____20119 =
                                     delta_depth_of_term env1 head2  in
                                   FStar_Util.bind_opt uu____20119
                                     (fun x  ->
                                        let uu____20126 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____20126)
                                    in
                                 FStar_Util.dflt "" uu____20115  in
                               FStar_Util.format4
                                 "head mismatch (%s (%s) vs %s (%s))"
                                 uu____20091 uu____20093 uu____20111
                                 uu____20113
                                in
                             giveup env1 uu____20089 orig))
                 | (HeadMatch (true ),uu____20132) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20147 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20147 with
                        | (guard,wl2) ->
                            let uu____20154 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20154)
                     else
                       (let uu____20157 =
                          let uu____20159 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____20161 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____20159 uu____20161
                           in
                        giveup env1 uu____20157 orig)
                 | (uu____20164,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2822_20178 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2822_20178.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2822_20178.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2822_20178.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2822_20178.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2822_20178.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2822_20178.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2822_20178.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2822_20178.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20205 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20205
          then
            let uu____20208 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20208
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20214 =
                let uu____20217 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20217  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20214 t1);
             (let uu____20236 =
                let uu____20239 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20239  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20236 t2);
             (let uu____20258 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20258
              then
                let uu____20262 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20264 =
                  let uu____20266 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20268 =
                    let uu____20270 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____20270  in
                  Prims.op_Hat uu____20266 uu____20268  in
                let uu____20273 =
                  let uu____20275 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20277 =
                    let uu____20279 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____20279  in
                  Prims.op_Hat uu____20275 uu____20277  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20262 uu____20264 uu____20273
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20286,uu____20287) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20311,FStar_Syntax_Syntax.Tm_delayed uu____20312) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20336,uu____20337) ->
                  let uu____20364 =
                    let uu___2853_20365 = problem  in
                    let uu____20366 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2853_20365.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20366;
                      FStar_TypeChecker_Common.relation =
                        (uu___2853_20365.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2853_20365.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2853_20365.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2853_20365.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2853_20365.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2853_20365.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2853_20365.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2853_20365.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20364 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20367,uu____20368) ->
                  let uu____20375 =
                    let uu___2859_20376 = problem  in
                    let uu____20377 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2859_20376.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20377;
                      FStar_TypeChecker_Common.relation =
                        (uu___2859_20376.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2859_20376.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2859_20376.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2859_20376.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2859_20376.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2859_20376.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2859_20376.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2859_20376.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20375 wl
              | (uu____20378,FStar_Syntax_Syntax.Tm_ascribed uu____20379) ->
                  let uu____20406 =
                    let uu___2865_20407 = problem  in
                    let uu____20408 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2865_20407.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2865_20407.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2865_20407.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20408;
                      FStar_TypeChecker_Common.element =
                        (uu___2865_20407.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2865_20407.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2865_20407.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2865_20407.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2865_20407.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2865_20407.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20406 wl
              | (uu____20409,FStar_Syntax_Syntax.Tm_meta uu____20410) ->
                  let uu____20417 =
                    let uu___2871_20418 = problem  in
                    let uu____20419 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2871_20418.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2871_20418.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2871_20418.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20419;
                      FStar_TypeChecker_Common.element =
                        (uu___2871_20418.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2871_20418.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2871_20418.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2871_20418.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2871_20418.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2871_20418.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20417 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____20421),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____20423)) ->
                  let uu____20432 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____20432
              | (FStar_Syntax_Syntax.Tm_bvar uu____20433,uu____20434) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____20436,FStar_Syntax_Syntax.Tm_bvar uu____20437) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___29_20507 =
                    match uu___29_20507 with
                    | [] -> c
                    | bs ->
                        let uu____20535 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____20535
                     in
                  let uu____20546 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____20546 with
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
                                    let uu____20695 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____20695
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
                  let mk_t t l uu___30_20784 =
                    match uu___30_20784 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____20826 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____20826 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____20971 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____20972 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____20971
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____20972 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____20974,uu____20975) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21006 -> true
                    | uu____21026 -> false  in
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
                      (let uu____21086 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___2973_21094 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___2973_21094.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___2973_21094.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___2973_21094.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___2973_21094.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___2973_21094.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___2973_21094.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___2973_21094.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___2973_21094.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___2973_21094.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___2973_21094.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___2973_21094.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___2973_21094.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___2973_21094.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___2973_21094.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___2973_21094.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___2973_21094.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___2973_21094.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___2973_21094.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___2973_21094.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___2973_21094.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___2973_21094.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___2973_21094.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___2973_21094.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___2973_21094.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___2973_21094.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___2973_21094.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___2973_21094.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___2973_21094.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___2973_21094.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___2973_21094.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___2973_21094.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___2973_21094.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
                                (uu___2967_21047.FStar_TypeChecker_Env.synth_hook);
=======
                                (uu___2973_21094.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___2973_21094.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> cp debugging an issue
                              FStar_TypeChecker_Env.splice =
                                (uu___2973_21094.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___2973_21094.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___2973_21094.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___2973_21094.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___2973_21094.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___2973_21094.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___2973_21094.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___2973_21094.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___2973_21094.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21086 with
                       | (uu____21099,ty,uu____21101) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21110 =
                                 let uu____21111 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21111.FStar_Syntax_Syntax.n  in
                               match uu____21110 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21114 ->
                                   let uu____21121 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21121
                               | uu____21122 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21125 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21125
                             then
                               let uu____21130 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21132 =
                                 let uu____21134 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21134
                                  in
                               let uu____21135 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21130 uu____21132 uu____21135
                             else ());
                            r1))
                     in
                  let uu____21140 =
                    let uu____21157 = maybe_eta t1  in
                    let uu____21164 = maybe_eta t2  in
                    (uu____21157, uu____21164)  in
                  (match uu____21140 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___2994_21206 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___2994_21206.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___2994_21206.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___2994_21206.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___2994_21206.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___2994_21206.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___2994_21206.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___2994_21206.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___2994_21206.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21227 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21227
                       then
                         let uu____21230 = destruct_flex_t not_abs wl  in
                         (match uu____21230 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3011_21247 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3011_21247.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3011_21247.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3011_21247.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3011_21247.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3011_21247.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3011_21247.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3011_21247.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3011_21247.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21271 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21271
                       then
                         let uu____21274 = destruct_flex_t not_abs wl  in
                         (match uu____21274 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3011_21291 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3011_21291.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3011_21291.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3011_21291.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3011_21291.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3011_21291.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3011_21291.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3011_21291.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3011_21291.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____21295 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21313,FStar_Syntax_Syntax.Tm_abs uu____21314) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21345 -> true
                    | uu____21365 -> false  in
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
                      (let uu____21425 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___2973_21433 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___2973_21433.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___2973_21433.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___2973_21433.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___2973_21433.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___2973_21433.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___2973_21433.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___2973_21433.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___2973_21433.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___2973_21433.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___2973_21433.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___2973_21433.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___2973_21433.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___2973_21433.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___2973_21433.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___2973_21433.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___2973_21433.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___2973_21433.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___2973_21433.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___2973_21433.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___2973_21433.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___2973_21433.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___2973_21433.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___2973_21433.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___2973_21433.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___2973_21433.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___2973_21433.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___2973_21433.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___2973_21433.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___2973_21433.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___2973_21433.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___2973_21433.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___2973_21433.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
                                (uu___2967_21386.FStar_TypeChecker_Env.synth_hook);
=======
                                (uu___2973_21433.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___2973_21433.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> cp debugging an issue
                              FStar_TypeChecker_Env.splice =
                                (uu___2973_21433.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___2973_21433.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___2973_21433.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___2973_21433.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___2973_21433.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___2973_21433.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___2973_21433.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___2973_21433.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___2973_21433.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21425 with
                       | (uu____21438,ty,uu____21440) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21449 =
                                 let uu____21450 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21450.FStar_Syntax_Syntax.n  in
                               match uu____21449 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21453 ->
                                   let uu____21460 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21460
                               | uu____21461 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21464 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21464
                             then
                               let uu____21469 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21471 =
                                 let uu____21473 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21473
                                  in
                               let uu____21474 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21469 uu____21471 uu____21474
                             else ());
                            r1))
                     in
                  let uu____21479 =
                    let uu____21496 = maybe_eta t1  in
                    let uu____21503 = maybe_eta t2  in
                    (uu____21496, uu____21503)  in
                  (match uu____21479 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___2994_21545 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___2994_21545.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___2994_21545.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___2994_21545.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___2994_21545.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___2994_21545.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___2994_21545.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___2994_21545.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___2994_21545.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21566 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21566
                       then
                         let uu____21569 = destruct_flex_t not_abs wl  in
                         (match uu____21569 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3011_21586 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3011_21586.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3011_21586.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3011_21586.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3011_21586.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3011_21586.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3011_21586.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3011_21586.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3011_21586.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21610 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21610
                       then
                         let uu____21613 = destruct_flex_t not_abs wl  in
                         (match uu____21613 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3011_21630 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3011_21630.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3011_21630.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3011_21630.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3011_21630.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3011_21630.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3011_21630.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3011_21630.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3011_21630.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____21634 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____21664 =
                    let uu____21669 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____21669 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3034_21697 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3034_21697.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3034_21697.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3036_21699 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3036_21699.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3036_21699.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____21700,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3034_21715 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3034_21715.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3034_21715.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3036_21717 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3036_21717.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3036_21717.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____21718 -> (x1, x2)  in
                  (match uu____21664 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____21737 = as_refinement false env t11  in
                       (match uu____21737 with
                        | (x12,phi11) ->
                            let uu____21745 = as_refinement false env t21  in
                            (match uu____21745 with
                             | (x22,phi21) ->
                                 ((let uu____21754 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21754
                                   then
                                     ((let uu____21759 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____21761 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21763 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____21759
                                         uu____21761 uu____21763);
                                      (let uu____21766 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____21768 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21770 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____21766
                                         uu____21768 uu____21770))
                                   else ());
                                  (let uu____21775 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____21775 with
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
                                         let uu____21846 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____21846
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____21858 =
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
                                         (let uu____21871 =
                                            let uu____21874 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____21874
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____21871
                                            (p_guard base_prob));
                                         (let uu____21893 =
                                            let uu____21896 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____21896
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____21893
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____21915 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____21915)
                                          in
                                       let has_uvars =
                                         (let uu____21920 =
                                            let uu____21922 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____21922
                                             in
                                          Prims.op_Negation uu____21920) ||
                                           (let uu____21926 =
                                              let uu____21928 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____21928
                                               in
                                            Prims.op_Negation uu____21926)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____21932 =
                                           let uu____21937 =
                                             let uu____21946 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____21946]  in
                                           mk_t_problem wl1 uu____21937 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____21932 with
                                          | (ref_prob,wl2) ->
                                              let uu____21968 =
                                                solve env1
                                                  (let uu___3078_21970 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3078_21970.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3078_21970.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3078_21970.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3078_21970.tcenv);
                                                     wl_implicits =
                                                       (uu___3078_21970.wl_implicits)
                                                   })
                                                 in
                                              (match uu____21968 with
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
                                               | Success uu____21987 ->
                                                   let guard =
                                                     let uu____21995 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____21995
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___3089_22004 =
                                                       wl3  in
                                                     {
                                                       attempting =
                                                         (uu___3089_22004.attempting);
                                                       wl_deferred =
                                                         (uu___3089_22004.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            Prims.int_one);
                                                       defer_ok =
                                                         (uu___3089_22004.defer_ok);
                                                       smt_ok =
                                                         (uu___3089_22004.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___3089_22004.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___3089_22004.tcenv);
                                                       wl_implicits =
                                                         (uu___3089_22004.wl_implicits)
                                                     }  in
                                                   let uu____22006 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____22006))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22009,FStar_Syntax_Syntax.Tm_uvar uu____22010) ->
                  let uu____22035 = destruct_flex_t t1 wl  in
                  (match uu____22035 with
                   | (f1,wl1) ->
                       let uu____22042 = destruct_flex_t t2 wl1  in
                       (match uu____22042 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22049;
                    FStar_Syntax_Syntax.pos = uu____22050;
                    FStar_Syntax_Syntax.vars = uu____22051;_},uu____22052),FStar_Syntax_Syntax.Tm_uvar
                 uu____22053) ->
                  let uu____22102 = destruct_flex_t t1 wl  in
                  (match uu____22102 with
                   | (f1,wl1) ->
                       let uu____22109 = destruct_flex_t t2 wl1  in
                       (match uu____22109 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22116,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22117;
                    FStar_Syntax_Syntax.pos = uu____22118;
                    FStar_Syntax_Syntax.vars = uu____22119;_},uu____22120))
                  ->
                  let uu____22169 = destruct_flex_t t1 wl  in
                  (match uu____22169 with
                   | (f1,wl1) ->
                       let uu____22176 = destruct_flex_t t2 wl1  in
                       (match uu____22176 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22183;
                    FStar_Syntax_Syntax.pos = uu____22184;
                    FStar_Syntax_Syntax.vars = uu____22185;_},uu____22186),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22187;
                    FStar_Syntax_Syntax.pos = uu____22188;
                    FStar_Syntax_Syntax.vars = uu____22189;_},uu____22190))
                  ->
                  let uu____22263 = destruct_flex_t t1 wl  in
                  (match uu____22263 with
                   | (f1,wl1) ->
                       let uu____22270 = destruct_flex_t t2 wl1  in
                       (match uu____22270 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22277,uu____22278) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22291 = destruct_flex_t t1 wl  in
                  (match uu____22291 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22298;
                    FStar_Syntax_Syntax.pos = uu____22299;
                    FStar_Syntax_Syntax.vars = uu____22300;_},uu____22301),uu____22302)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22339 = destruct_flex_t t1 wl  in
                  (match uu____22339 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22346,FStar_Syntax_Syntax.Tm_uvar uu____22347) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22360,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22361;
                    FStar_Syntax_Syntax.pos = uu____22362;
                    FStar_Syntax_Syntax.vars = uu____22363;_},uu____22364))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22401,FStar_Syntax_Syntax.Tm_arrow uu____22402) ->
                  solve_t' env
                    (let uu___3189_22430 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3189_22430.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3189_22430.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3189_22430.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3189_22430.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3189_22430.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3189_22430.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3189_22430.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3189_22430.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3189_22430.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22431;
                    FStar_Syntax_Syntax.pos = uu____22432;
                    FStar_Syntax_Syntax.vars = uu____22433;_},uu____22434),FStar_Syntax_Syntax.Tm_arrow
                 uu____22435) ->
                  solve_t' env
                    (let uu___3189_22487 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3189_22487.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3189_22487.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3189_22487.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3189_22487.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3189_22487.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3189_22487.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3189_22487.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3189_22487.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3189_22487.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22488,FStar_Syntax_Syntax.Tm_uvar uu____22489) ->
                  let uu____22502 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22502
              | (uu____22503,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22504;
                    FStar_Syntax_Syntax.pos = uu____22505;
                    FStar_Syntax_Syntax.vars = uu____22506;_},uu____22507))
                  ->
                  let uu____22544 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22544
              | (FStar_Syntax_Syntax.Tm_uvar uu____22545,uu____22546) ->
                  let uu____22559 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22559
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22560;
                    FStar_Syntax_Syntax.pos = uu____22561;
                    FStar_Syntax_Syntax.vars = uu____22562;_},uu____22563),uu____22564)
                  ->
                  let uu____22601 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22601
              | (FStar_Syntax_Syntax.Tm_refine uu____22602,uu____22603) ->
                  let t21 =
                    let uu____22611 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____22611  in
                  solve_t env
                    (let uu___3224_22637 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3224_22637.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3224_22637.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3224_22637.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3224_22637.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3224_22637.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3224_22637.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3224_22637.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3224_22637.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3224_22637.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22638,FStar_Syntax_Syntax.Tm_refine uu____22639) ->
                  let t11 =
                    let uu____22647 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22647  in
                  solve_t env
                    (let uu___3231_22673 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3231_22673.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3231_22673.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3231_22673.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3231_22673.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3231_22673.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3231_22673.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3231_22673.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3231_22673.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3231_22673.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____22755 =
                    let uu____22756 = guard_of_prob env wl problem t1 t2  in
                    match uu____22756 with
                    | (guard,wl1) ->
                        let uu____22763 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____22763
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____22982 = br1  in
                        (match uu____22982 with
                         | (p1,w1,uu____23011) ->
                             let uu____23028 = br2  in
                             (match uu____23028 with
                              | (p2,w2,uu____23051) ->
                                  let uu____23056 =
                                    let uu____23058 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23058  in
                                  if uu____23056
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23085 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23085 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23122 = br2  in
                                         (match uu____23122 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23155 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23155
                                                 in
                                              let uu____23160 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23191,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23212) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23271 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23271 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23160
                                                (fun uu____23343  ->
                                                   match uu____23343 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23380 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23380
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____23401
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____23401
                                                              then
                                                                let uu____23406
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____23408
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____23406
                                                                  uu____23408
                                                              else ());
                                                             (let uu____23414
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____23414
                                                                (fun
                                                                   uu____23450
                                                                    ->
                                                                   match uu____23450
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
                    | uu____23579 -> FStar_Pervasives_Native.None  in
                  let uu____23620 = solve_branches wl brs1 brs2  in
                  (match uu____23620 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____23671 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____23671 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____23705 =
                                FStar_List.map
                                  (fun uu____23717  ->
                                     match uu____23717 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____23705  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____23726 =
                              let uu____23727 =
                                let uu____23728 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____23728
                                  (let uu___3330_23736 = wl3  in
                                   {
                                     attempting =
                                       (uu___3330_23736.attempting);
                                     wl_deferred =
                                       (uu___3330_23736.wl_deferred);
                                     ctr = (uu___3330_23736.ctr);
                                     defer_ok = (uu___3330_23736.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3330_23736.umax_heuristic_ok);
                                     tcenv = (uu___3330_23736.tcenv);
                                     wl_implicits =
                                       (uu___3330_23736.wl_implicits)
                                   })
                                 in
                              solve env uu____23727  in
                            (match uu____23726 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____23741 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____23748,uu____23749) ->
                  let head1 =
                    let uu____23773 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23773
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23819 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23819
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23865 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23865
                    then
                      let uu____23869 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23871 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23873 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23869 uu____23871 uu____23873
                    else ());
                   (let no_free_uvars t =
                      (let uu____23887 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23887) &&
                        (let uu____23891 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23891)
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
                      let uu____23908 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23908 = FStar_Syntax_Util.Equal  in
                    let uu____23909 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23909
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23913 = equal t1 t2  in
                         (if uu____23913
                          then
                            let uu____23916 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____23916
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23921 =
                            let uu____23928 = equal t1 t2  in
                            if uu____23928
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23941 = mk_eq2 wl env orig t1 t2  in
                               match uu____23941 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____23921 with
                          | (guard,wl1) ->
                              let uu____23962 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____23962))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____23965,uu____23966) ->
                  let head1 =
                    let uu____23974 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23974
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24020 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24020
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24066 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24066
                    then
                      let uu____24070 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24072 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24074 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24070 uu____24072 uu____24074
                    else ());
                   (let no_free_uvars t =
                      (let uu____24088 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24088) &&
                        (let uu____24092 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24092)
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
                      let uu____24109 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24109 = FStar_Syntax_Util.Equal  in
                    let uu____24110 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24110
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24114 = equal t1 t2  in
                         (if uu____24114
                          then
                            let uu____24117 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24117
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24122 =
                            let uu____24129 = equal t1 t2  in
                            if uu____24129
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24142 = mk_eq2 wl env orig t1 t2  in
                               match uu____24142 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24122 with
                          | (guard,wl1) ->
                              let uu____24163 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24163))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24166,uu____24167) ->
                  let head1 =
                    let uu____24169 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24169
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24215 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24215
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24261 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24261
                    then
                      let uu____24265 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24267 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24269 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24265 uu____24267 uu____24269
                    else ());
                   (let no_free_uvars t =
                      (let uu____24283 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24283) &&
                        (let uu____24287 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24287)
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
                      let uu____24304 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24304 = FStar_Syntax_Util.Equal  in
                    let uu____24305 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24305
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24309 = equal t1 t2  in
                         (if uu____24309
                          then
                            let uu____24312 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24312
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24317 =
                            let uu____24324 = equal t1 t2  in
                            if uu____24324
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24337 = mk_eq2 wl env orig t1 t2  in
                               match uu____24337 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24317 with
                          | (guard,wl1) ->
                              let uu____24358 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24358))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24361,uu____24362) ->
                  let head1 =
                    let uu____24364 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24364
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24410 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24410
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24456 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24456
                    then
                      let uu____24460 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24462 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24464 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24460 uu____24462 uu____24464
                    else ());
                   (let no_free_uvars t =
                      (let uu____24478 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24478) &&
                        (let uu____24482 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24482)
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
                      let uu____24499 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24499 = FStar_Syntax_Util.Equal  in
                    let uu____24500 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24500
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24504 = equal t1 t2  in
                         (if uu____24504
                          then
                            let uu____24507 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24507
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24512 =
                            let uu____24519 = equal t1 t2  in
                            if uu____24519
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24532 = mk_eq2 wl env orig t1 t2  in
                               match uu____24532 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24512 with
                          | (guard,wl1) ->
                              let uu____24553 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24553))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____24556,uu____24557) ->
                  let head1 =
                    let uu____24559 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24559
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24605 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24605
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24651 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24651
                    then
                      let uu____24655 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24657 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24659 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24655 uu____24657 uu____24659
                    else ());
                   (let no_free_uvars t =
                      (let uu____24673 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24673) &&
                        (let uu____24677 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24677)
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
                      let uu____24694 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24694 = FStar_Syntax_Util.Equal  in
                    let uu____24695 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24695
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24699 = equal t1 t2  in
                         (if uu____24699
                          then
                            let uu____24702 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24702
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24707 =
                            let uu____24714 = equal t1 t2  in
                            if uu____24714
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24727 = mk_eq2 wl env orig t1 t2  in
                               match uu____24727 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24707 with
                          | (guard,wl1) ->
                              let uu____24748 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24748))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____24751,uu____24752) ->
                  let head1 =
                    let uu____24770 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24770
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24816 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24816
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24862 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24862
                    then
                      let uu____24866 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24868 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24870 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24866 uu____24868 uu____24870
                    else ());
                   (let no_free_uvars t =
                      (let uu____24884 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24884) &&
                        (let uu____24888 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24888)
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
                      let uu____24905 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24905 = FStar_Syntax_Util.Equal  in
                    let uu____24906 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24906
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24910 = equal t1 t2  in
                         (if uu____24910
                          then
                            let uu____24913 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24913
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24918 =
                            let uu____24925 = equal t1 t2  in
                            if uu____24925
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24938 = mk_eq2 wl env orig t1 t2  in
                               match uu____24938 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24918 with
                          | (guard,wl1) ->
                              let uu____24959 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24959))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24962,FStar_Syntax_Syntax.Tm_match uu____24963) ->
                  let head1 =
                    let uu____24987 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24987
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25033 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25033
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25079 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25079
                    then
                      let uu____25083 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25085 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25087 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25083 uu____25085 uu____25087
                    else ());
                   (let no_free_uvars t =
                      (let uu____25101 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25101) &&
                        (let uu____25105 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25105)
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
                      let uu____25122 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25122 = FStar_Syntax_Util.Equal  in
                    let uu____25123 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25123
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25127 = equal t1 t2  in
                         (if uu____25127
                          then
                            let uu____25130 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25130
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25135 =
                            let uu____25142 = equal t1 t2  in
                            if uu____25142
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25155 = mk_eq2 wl env orig t1 t2  in
                               match uu____25155 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25135 with
                          | (guard,wl1) ->
                              let uu____25176 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25176))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25179,FStar_Syntax_Syntax.Tm_uinst uu____25180) ->
                  let head1 =
                    let uu____25188 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25188
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25228 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25228
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25268 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25268
                    then
                      let uu____25272 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25274 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25276 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25272 uu____25274 uu____25276
                    else ());
                   (let no_free_uvars t =
                      (let uu____25290 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25290) &&
                        (let uu____25294 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25294)
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
                      let uu____25311 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25311 = FStar_Syntax_Util.Equal  in
                    let uu____25312 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25312
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25316 = equal t1 t2  in
                         (if uu____25316
                          then
                            let uu____25319 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25319
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25324 =
                            let uu____25331 = equal t1 t2  in
                            if uu____25331
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25344 = mk_eq2 wl env orig t1 t2  in
                               match uu____25344 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25324 with
                          | (guard,wl1) ->
                              let uu____25365 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25365))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25368,FStar_Syntax_Syntax.Tm_name uu____25369) ->
                  let head1 =
                    let uu____25371 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25371
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25411 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25411
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25451 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25451
                    then
                      let uu____25455 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25457 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25459 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25455 uu____25457 uu____25459
                    else ());
                   (let no_free_uvars t =
                      (let uu____25473 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25473) &&
                        (let uu____25477 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25477)
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
                      let uu____25494 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25494 = FStar_Syntax_Util.Equal  in
                    let uu____25495 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25495
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25499 = equal t1 t2  in
                         (if uu____25499
                          then
                            let uu____25502 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25502
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25507 =
                            let uu____25514 = equal t1 t2  in
                            if uu____25514
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25527 = mk_eq2 wl env orig t1 t2  in
                               match uu____25527 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25507 with
                          | (guard,wl1) ->
                              let uu____25548 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25548))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25551,FStar_Syntax_Syntax.Tm_constant uu____25552) ->
                  let head1 =
                    let uu____25554 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25554
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25594 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25594
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25634 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25634
                    then
                      let uu____25638 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25640 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25642 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25638 uu____25640 uu____25642
                    else ());
                   (let no_free_uvars t =
                      (let uu____25656 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25656) &&
                        (let uu____25660 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25660)
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
                      let uu____25677 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25677 = FStar_Syntax_Util.Equal  in
                    let uu____25678 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25678
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25682 = equal t1 t2  in
                         (if uu____25682
                          then
                            let uu____25685 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25685
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25690 =
                            let uu____25697 = equal t1 t2  in
                            if uu____25697
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25710 = mk_eq2 wl env orig t1 t2  in
                               match uu____25710 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25690 with
                          | (guard,wl1) ->
                              let uu____25731 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25731))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25734,FStar_Syntax_Syntax.Tm_fvar uu____25735) ->
                  let head1 =
                    let uu____25737 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25737
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25777 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25777
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25817 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25817
                    then
                      let uu____25821 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25823 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25825 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25821 uu____25823 uu____25825
                    else ());
                   (let no_free_uvars t =
                      (let uu____25839 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25839) &&
                        (let uu____25843 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25843)
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
                      let uu____25860 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25860 = FStar_Syntax_Util.Equal  in
                    let uu____25861 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25861
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25865 = equal t1 t2  in
                         (if uu____25865
                          then
                            let uu____25868 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25868
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25873 =
                            let uu____25880 = equal t1 t2  in
                            if uu____25880
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25893 = mk_eq2 wl env orig t1 t2  in
                               match uu____25893 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25873 with
                          | (guard,wl1) ->
                              let uu____25914 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25914))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25917,FStar_Syntax_Syntax.Tm_app uu____25918) ->
                  let head1 =
                    let uu____25936 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25936
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25976 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25976
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26016 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26016
                    then
                      let uu____26020 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26022 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26024 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26020 uu____26022 uu____26024
                    else ());
                   (let no_free_uvars t =
                      (let uu____26038 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26038) &&
                        (let uu____26042 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26042)
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
                      let uu____26059 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26059 = FStar_Syntax_Util.Equal  in
                    let uu____26060 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26060
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26064 = equal t1 t2  in
                         (if uu____26064
                          then
                            let uu____26067 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26067
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26072 =
                            let uu____26079 = equal t1 t2  in
                            if uu____26079
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26092 = mk_eq2 wl env orig t1 t2  in
                               match uu____26092 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26072 with
                          | (guard,wl1) ->
                              let uu____26113 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26113))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26116,FStar_Syntax_Syntax.Tm_let uu____26117) ->
                  let uu____26144 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26144
                  then
                    let uu____26147 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26147
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____26151,uu____26152) ->
                  let uu____26166 =
                    let uu____26172 =
                      let uu____26174 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26176 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26178 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26180 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26174 uu____26176 uu____26178 uu____26180
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26172)
                     in
                  FStar_Errors.raise_error uu____26166
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26184,FStar_Syntax_Syntax.Tm_let uu____26185) ->
                  let uu____26199 =
                    let uu____26205 =
                      let uu____26207 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26209 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26211 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26213 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26207 uu____26209 uu____26211 uu____26213
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26205)
                     in
                  FStar_Errors.raise_error uu____26199
                    t1.FStar_Syntax_Syntax.pos
              | uu____26217 -> giveup env "head tag mismatch" orig))))

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
          (let uu____26286 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26286
           then
             let uu____26291 =
               let uu____26293 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26293  in
             let uu____26294 =
               let uu____26296 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26296  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26291 uu____26294
           else ());
          (let uu____26300 =
             let uu____26302 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26302  in
           if uu____26300
           then
             let uu____26305 =
               let uu____26307 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____26309 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____26307 uu____26309
                in
             giveup env uu____26305 orig
           else
             (let uu____26314 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____26314 with
              | (ret_sub_prob,wl1) ->
                  let uu____26322 =
                    FStar_List.fold_right2
                      (fun uu____26359  ->
                         fun uu____26360  ->
                           fun uu____26361  ->
                             match (uu____26359, uu____26360, uu____26361)
                             with
                             | ((a1,uu____26405),(a2,uu____26407),(arg_sub_probs,wl2))
                                 ->
                                 let uu____26440 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____26440 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____26322 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs =
                         let uu____26467 =
                           let uu____26470 =
                             FStar_All.pipe_right
                               g_lift.FStar_TypeChecker_Common.deferred
                               (FStar_List.map FStar_Pervasives_Native.snd)
                              in
                           FStar_List.append arg_sub_probs uu____26470  in
                         ret_sub_prob :: uu____26467  in
                       let guard =
                         let guard =
                           let uu____26492 = FStar_List.map p_guard sub_probs
                              in
                           FStar_Syntax_Util.mk_conj_l uu____26492  in
                         match g_lift.FStar_TypeChecker_Common.guard_f with
                         | FStar_TypeChecker_Common.Trivial  -> guard
                         | FStar_TypeChecker_Common.NonTrivial f ->
                             FStar_Syntax_Util.mk_conj guard f
                          in
                       let wl3 =
                         let uu___3467_26501 = wl2  in
                         {
                           attempting = (uu___3467_26501.attempting);
                           wl_deferred = (uu___3467_26501.wl_deferred);
                           ctr = (uu___3467_26501.ctr);
                           defer_ok = (uu___3467_26501.defer_ok);
                           smt_ok = (uu___3467_26501.smt_ok);
                           umax_heuristic_ok =
                             (uu___3467_26501.umax_heuristic_ok);
                           tcenv = (uu___3467_26501.tcenv);
                           wl_implicits =
                             (FStar_List.append
                                g_lift.FStar_TypeChecker_Common.implicits
                                wl2.wl_implicits)
                         }  in
                       let wl4 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl3
                          in
                       let uu____26503 = attempt sub_probs wl4  in
                       solve env uu____26503)))
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
                  (let uu____26524 =
                     FStar_TypeChecker_Env.is_layered_effect env
                       c11.FStar_Syntax_Syntax.effect_name
                      in
                   Prims.op_Negation uu____26524))
              in
           if Prims.op_Negation supported
           then
             let uu____26528 =
               let uu____26530 =
                 let uu____26532 =
                   FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
                 FStar_All.pipe_right uu____26532
                   FStar_Syntax_Print.comp_to_string
                  in
               let uu____26534 =
                 let uu____26536 =
                   FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
                 FStar_All.pipe_right uu____26536
                   FStar_Syntax_Print.comp_to_string
                  in
               FStar_Util.format2
                 "Unsupported case for solve_layered_sub c1: %s and c2: %s"
                 uu____26530 uu____26534
                in
             failwith uu____26528
           else ());
          (let uu____26542 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____26542
           then
             let uu____26547 =
               let uu____26549 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26549
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____26551 =
               let uu____26553 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26553
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____26547 uu____26551
           else ());
          (let uu____26558 =
             let uu____26563 =
               let uu____26568 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26568
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____26563
               (fun uu____26585  ->
                  match uu____26585 with
                  | (c,g) ->
                      let uu____26596 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____26596, g))
              in
           match uu____26558 with
           | (c12,g_lift) ->
               ((let uu____26600 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____26600
                 then
                   let uu____26605 =
                     let uu____26607 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26607
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____26609 =
                     let uu____26611 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26611
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____26605 uu____26609
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3491_26621 = wl  in
                     {
                       attempting = (uu___3491_26621.attempting);
                       wl_deferred = (uu___3491_26621.wl_deferred);
                       ctr = (uu___3491_26621.ctr);
                       defer_ok = (uu___3491_26621.defer_ok);
                       smt_ok = (uu___3491_26621.smt_ok);
                       umax_heuristic_ok =
                         (uu___3491_26621.umax_heuristic_ok);
                       tcenv = (uu___3491_26621.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
                   let uu____26622 =
                     let is_uvar1 t =
                       let uu____26636 =
                         let uu____26637 = FStar_Syntax_Subst.compress t  in
                         uu____26637.FStar_Syntax_Syntax.n  in
                       match uu____26636 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____26641 -> true
                       | FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_uvar uu____26655;
                              FStar_Syntax_Syntax.pos = uu____26656;
                              FStar_Syntax_Syntax.vars = uu____26657;_},uu____26658)
                           -> true
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_uvar uu____26676;
                              FStar_Syntax_Syntax.pos = uu____26677;
                              FStar_Syntax_Syntax.vars = uu____26678;_},uu____26679)
                           -> true
                       | uu____26717 -> false  in
                     FStar_List.fold_right2
                       (fun uu____26750  ->
                          fun uu____26751  ->
                            fun uu____26752  ->
                              match (uu____26750, uu____26751, uu____26752)
                              with
                              | ((a1,uu____26796),(a2,uu____26798),(is_sub_probs,wl2))
                                  ->
                                  let uu____26831 = is_uvar1 a1  in
                                  if uu____26831
                                  then
                                    let uu____26840 =
                                      sub_prob wl2 a1
                                        FStar_TypeChecker_Common.EQ a2
                                        "l.h.s. effect index uvar"
                                       in
                                    (match uu____26840 with
                                     | (p,wl3) -> ((p :: is_sub_probs), wl3))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____26622 with
                   | (is_sub_probs,wl2) ->
                       let uu____26868 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____26868 with
                        | (ret_sub_prob,wl3) ->
                            let uu____26876 =
                              let uu____26881 =
                                FStar_All.pipe_right
                                  c21.FStar_Syntax_Syntax.effect_name
                                  (FStar_TypeChecker_Env.get_effect_decl env)
                                 in
                              FStar_All.pipe_right uu____26881
                                (fun ed  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with
                                     ed.FStar_Syntax_Syntax.stronger
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____26876 with
                             | (uu____26888,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____26899 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____26901 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____26899 s uu____26901
                                    in
                                 let uu____26904 =
                                   let uu____26933 =
                                     let uu____26934 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____26934.FStar_Syntax_Syntax.n  in
                                   match uu____26933 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____26994 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____26994 with
                                        | (a::bs1,c3) ->
                                            let uu____27050 =
                                              let uu____27069 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27069
                                                (fun uu____27173  ->
                                                   match uu____27173 with
                                                   | (l1,l2) ->
                                                       let uu____27246 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____27246))
                                               in
                                            (match uu____27050 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____27351 ->
                                       let uu____27352 =
                                         let uu____27358 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____27358)
                                          in
                                       FStar_Errors.raise_error uu____27352 r
                                    in
                                 (match uu____26904 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____27434 =
                                        let uu____27441 =
                                          let uu____27442 =
                                            let uu____27443 =
                                              let uu____27450 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____27450,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____27443
                                             in
                                          [uu____27442]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____27441
                                          (fun b  ->
                                             let uu____27466 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____27468 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____27470 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____27466 uu____27468
                                               uu____27470) r
                                         in
                                      (match uu____27434 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           let wl4 =
                                             let uu___3565_27480 = wl3  in
                                             {
                                               attempting =
                                                 (uu___3565_27480.attempting);
                                               wl_deferred =
                                                 (uu___3565_27480.wl_deferred);
                                               ctr = (uu___3565_27480.ctr);
                                               defer_ok =
                                                 (uu___3565_27480.defer_ok);
                                               smt_ok =
                                                 (uu___3565_27480.smt_ok);
                                               umax_heuristic_ok =
                                                 (uu___3565_27480.umax_heuristic_ok);
                                               tcenv =
                                                 (uu___3565_27480.tcenv);
                                               wl_implicits =
                                                 (FStar_List.append
                                                    g_uvars.FStar_TypeChecker_Common.implicits
                                                    wl3.wl_implicits)
                                             }  in
                                           let substs =
                                             FStar_List.map2
                                               (fun b  ->
                                                  fun t  ->
                                                    let uu____27505 =
                                                      let uu____27512 =
                                                        FStar_All.pipe_right
                                                          b
                                                          FStar_Pervasives_Native.fst
                                                         in
                                                      (uu____27512, t)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____27505) (a_b ::
                                               rest_bs)
                                               ((c21.FStar_Syntax_Syntax.result_typ)
                                               :: rest_bs_uvars)
                                              in
                                           let uu____27529 =
                                             let f_sort_is =
                                               let uu____27539 =
                                                 let uu____27540 =
                                                   let uu____27543 =
                                                     let uu____27544 =
                                                       FStar_All.pipe_right
                                                         f_b
                                                         FStar_Pervasives_Native.fst
                                                        in
                                                     uu____27544.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Subst.compress
                                                     uu____27543
                                                    in
                                                 uu____27540.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____27539 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____27555,uu____27556::is)
                                                   ->
                                                   let uu____27598 =
                                                     FStar_All.pipe_right is
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____27598
                                                     (FStar_List.map
                                                        (FStar_Syntax_Subst.subst
                                                           substs))
                                               | uu____27631 ->
                                                   let uu____27632 =
                                                     let uu____27638 =
                                                       stronger_t_shape_error
                                                         "type of f is not a repr type"
                                                        in
                                                     (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                       uu____27638)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____27632 r
                                                in
                                             let uu____27644 =
                                               FStar_All.pipe_right
                                                 c12.FStar_Syntax_Syntax.effect_args
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_List.fold_left2
                                               (fun uu____27679  ->
                                                  fun f_sort_i  ->
                                                    fun c1_i  ->
                                                      match uu____27679 with
                                                      | (ps,wl5) ->
                                                          let uu____27700 =
                                                            sub_prob wl5
                                                              f_sort_i
                                                              FStar_TypeChecker_Common.EQ
                                                              c1_i
                                                              "indices of c1"
                                                             in
                                                          (match uu____27700
                                                           with
                                                           | (p,wl6) ->
                                                               ((FStar_List.append
                                                                   ps 
                                                                   [p]), wl6)))
                                               ([], wl4) f_sort_is
                                               uu____27644
                                              in
                                           (match uu____27529 with
                                            | (f_sub_probs,wl5) ->
                                                let stronger_ct =
                                                  let uu____27725 =
                                                    FStar_All.pipe_right
                                                      stronger_c
                                                      (FStar_Syntax_Subst.subst_comp
                                                         substs)
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____27725
                                                    FStar_Syntax_Util.comp_to_comp_typ
                                                   in
                                                let uu____27726 =
                                                  let g_sort_is =
                                                    let uu____27736 =
                                                      let uu____27737 =
                                                        FStar_Syntax_Subst.compress
                                                          stronger_ct.FStar_Syntax_Syntax.result_typ
                                                         in
                                                      uu____27737.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____27736 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (uu____27742,uu____27743::is)
                                                        ->
                                                        FStar_All.pipe_right
                                                          is
                                                          (FStar_List.map
                                                             FStar_Pervasives_Native.fst)
                                                    | uu____27811 ->
                                                        let uu____27812 =
                                                          let uu____27818 =
                                                            stronger_t_shape_error
                                                              "return type is not a repr type"
                                                             in
                                                          (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                            uu____27818)
                                                           in
                                                        FStar_Errors.raise_error
                                                          uu____27812 r
                                                     in
                                                  let uu____27824 =
                                                    FStar_All.pipe_right
                                                      c21.FStar_Syntax_Syntax.effect_args
                                                      (FStar_List.map
                                                         FStar_Pervasives_Native.fst)
                                                     in
                                                  FStar_List.fold_left2
                                                    (fun uu____27859  ->
                                                       fun g_sort_i  ->
                                                         fun c2_i  ->
                                                           match uu____27859
                                                           with
                                                           | (ps,wl6) ->
                                                               let uu____27880
                                                                 =
                                                                 sub_prob wl6
                                                                   g_sort_i
                                                                   FStar_TypeChecker_Common.EQ
                                                                   c2_i
                                                                   "indices of c2"
                                                                  in
                                                               (match uu____27880
                                                                with
                                                                | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                    ([], wl5) g_sort_is
                                                    uu____27824
                                                   in
                                                (match uu____27726 with
                                                 | (g_sub_probs,wl6) ->
                                                     let fml =
                                                       let uu____27907 =
                                                         let uu____27912 =
                                                           FStar_List.hd
                                                             stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                            in
                                                         let uu____27913 =
                                                           let uu____27914 =
                                                             FStar_List.hd
                                                               stronger_ct.FStar_Syntax_Syntax.effect_args
                                                              in
                                                           FStar_Pervasives_Native.fst
                                                             uu____27914
                                                            in
                                                         (uu____27912,
                                                           uu____27913)
                                                          in
                                                       match uu____27907 with
                                                       | (u,wp) ->
                                                           let trivial_post =
                                                             let ts =
                                                               let uu____27941
                                                                 =
                                                                 FStar_TypeChecker_Env.lookup_definition
                                                                   [FStar_TypeChecker_Env.NoDelta]
                                                                   env
                                                                   FStar_Parser_Const.trivial_pure_post_lid
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____27941
                                                                 FStar_Util.must
                                                                in
                                                             let uu____27958
                                                               =
                                                               FStar_TypeChecker_Env.inst_tscheme_with
                                                                 ts [u]
                                                                in
                                                             match uu____27958
                                                             with
                                                             | (uu____27963,t)
                                                                 ->
                                                                 let uu____27965
                                                                   =
                                                                   let uu____27970
                                                                    =
                                                                    let uu____27971
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    stronger_ct.FStar_Syntax_Syntax.result_typ
                                                                    FStar_Syntax_Syntax.as_arg
                                                                     in
                                                                    [uu____27971]
                                                                     in
                                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                                    t
                                                                    uu____27970
                                                                    in
                                                                 uu____27965
                                                                   FStar_Pervasives_Native.None
                                                                   FStar_Range.dummyRange
                                                              in
                                                           let uu____28004 =
                                                             let uu____28009
                                                               =
                                                               let uu____28010
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   trivial_post
                                                                   FStar_Syntax_Syntax.as_arg
                                                                  in
                                                               [uu____28010]
                                                                in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               wp uu____28009
                                                              in
                                                           uu____28004
                                                             FStar_Pervasives_Native.None
                                                             FStar_Range.dummyRange
                                                        in
                                                     let sub_probs =
                                                       let uu____28046 =
                                                         let uu____28049 =
                                                           let uu____28052 =
                                                             let uu____28055
                                                               =
                                                               FStar_All.pipe_right
                                                                 g_lift.FStar_TypeChecker_Common.deferred
                                                                 (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                in
                                                             FStar_List.append
                                                               g_sub_probs
                                                               uu____28055
                                                              in
                                                           FStar_List.append
                                                             f_sub_probs
                                                             uu____28052
                                                            in
                                                         FStar_List.append
                                                           is_sub_probs
                                                           uu____28049
                                                          in
                                                       ret_sub_prob ::
                                                         uu____28046
                                                        in
                                                     let guard =
                                                       let guard =
                                                         let uu____28079 =
                                                           FStar_List.map
                                                             p_guard
                                                             sub_probs
                                                            in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____28079
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
                                                       let uu____28090 =
                                                         let uu____28093 =
                                                           FStar_Syntax_Util.mk_conj
                                                             guard fml
                                                            in
                                                         FStar_All.pipe_left
                                                           (fun _28096  ->
                                                              FStar_Pervasives_Native.Some
                                                                _28096)
                                                           uu____28093
                                                          in
                                                       solve_prob orig
                                                         uu____28090 [] wl6
                                                        in
                                                     let uu____28097 =
                                                       attempt sub_probs wl7
                                                        in
                                                     solve env uu____28097)))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28120 =
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28122 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28122]
              | x -> x  in
            let c12 =
              let uu___3636_28125 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs1;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3636_28125.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3636_28125.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3636_28125.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3636_28125.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28126 =
              let uu____28131 =
                FStar_All.pipe_right
                  (let uu___3639_28133 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs1;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3639_28133.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3639_28133.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3639_28133.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3639_28133.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28131
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28126
              (fun uu____28147  ->
                 match uu____28147 with
                 | (c,g) ->
                     let uu____28154 =
                       let uu____28156 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28156  in
                     if uu____28154
                     then
                       let uu____28159 =
                         let uu____28165 =
                           let uu____28167 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28169 =
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                             uu____28167 uu____28169
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28165)
                          in
                       FStar_Errors.raise_error uu____28159 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28175 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28175
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
              (let uu____28181 = lift_c1 ()  in
               solve_eq uu____28181 c21 FStar_TypeChecker_Env.trivial_guard)
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
                      (fun uu___31_28190  ->
                         match uu___31_28190 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28195 -> false))
                  in
               let uu____28197 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28227)::uu____28228,(wp2,uu____28230)::uu____28231)
                     -> (wp1, wp2)
                 | uu____28304 ->
                     let uu____28329 =
                       let uu____28335 =
                         let uu____28337 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____28339 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____28337 uu____28339
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____28335)
                        in
                     FStar_Errors.raise_error uu____28329
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28197 with
               | (wpc1,wpc2) ->
                   let uu____28349 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____28349
                   then
                     let uu____28352 =
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28352 wl
                   else
                     (let uu____28356 =
                        let uu____28363 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____28363  in
                      match uu____28356 with
                      | (c2_decl,qualifiers) ->
                          let uu____28384 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____28384
                          then
                            let c1_repr =
                              let uu____28391 =
                                let uu____28392 =
                                  let uu____28393 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____28393  in
                                let uu____28394 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28392 uu____28394
                                 in
                              FStar_TypeChecker_Normalize.normalize
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28391
                               in
                            let c2_repr =
                              let uu____28396 =
                                let uu____28397 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____28398 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28397 uu____28398
                                 in
                              FStar_TypeChecker_Normalize.normalize
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28396
                               in
                            let uu____28399 =
                              let uu____28404 =
                                let uu____28406 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____28408 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____28406
                                  uu____28408
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____28404
                               in
                            (match uu____28399 with
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
                                 let uu____28414 = attempt [prob] wl2  in
                                 solve env uu____28414)
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
                               else
                                 (let wpc1_2 =
                                    let uu____28434 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____28434
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  if is_null_wp_2
                                  then
                                    ((let uu____28457 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____28457
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
                                      let uu____28469 =
                                        let uu____28476 =
                                          let uu____28477 =
                                            let uu____28494 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____28497 =
                                              let uu____28508 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____28508; wpc1_2]  in
                                            (uu____28494, uu____28497)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____28477
                                           in
                                        FStar_Syntax_Syntax.mk uu____28476
                                         in
                                      uu____28469
                                        FStar_Pervasives_Native.None r))
                                  else
                                    (let c2_univ =
                                       env.FStar_TypeChecker_Env.universe_of
                                         env
                                         c21.FStar_Syntax_Syntax.result_typ
                                        in
                                     let uu____28556 =
                                       let uu____28563 =
                                         let uu____28564 =
                                           let uu____28581 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl
                                               c2_decl.FStar_Syntax_Syntax.stronger
                                              in
                                           let uu____28584 =
                                             let uu____28595 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____28604 =
                                               let uu____28615 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____28615; wpc1_2]  in
                                             uu____28595 :: uu____28604  in
                                           (uu____28581, uu____28584)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____28564
                                          in
                                       FStar_Syntax_Syntax.mk uu____28563  in
                                     uu____28556 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____28669 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____28669
                              then
                                let uu____28674 =
                                  let uu____28676 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
                                    uu____28676
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____28674
                              else ());
                             (let uu____28680 =
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
                              match uu____28680 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____28689 =
                                      let uu____28692 =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
                                        (fun _28695  ->
                                           FStar_Pervasives_Native.Some
                                             _28695) uu____28692
                                       in
                                    solve_prob orig uu____28689 [] wl1  in
                                  let uu____28696 = attempt [base_prob] wl2
                                     in
                                  solve env uu____28696))))
           in
        let uu____28697 = FStar_Util.physical_equality c1 c2  in
        if uu____28697
        then
          let uu____28700 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____28700
        else
          ((let uu____28704 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____28704
            then
              let uu____28709 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____28711 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____28709
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____28711
            else ());
           (let uu____28716 =
              let uu____28725 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____28728 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____28725, uu____28728)  in
            match uu____28716 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____28746),FStar_Syntax_Syntax.Total
                    (t2,uu____28748)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____28765 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28765 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____28767,FStar_Syntax_Syntax.Total uu____28768) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____28787),FStar_Syntax_Syntax.Total
                    (t2,uu____28789)) ->
                     let uu____28806 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28806 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____28809),FStar_Syntax_Syntax.GTotal
                    (t2,uu____28811)) ->
                     let uu____28828 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28828 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____28831),FStar_Syntax_Syntax.GTotal
                    (t2,uu____28833)) ->
                     if
                       problem.FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.SUB
                     then
                       let uu____28851 =
                         problem_using_guard orig t1
                           problem.FStar_TypeChecker_Common.relation t2
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____28851 wl
                     else giveup env "GTot =/= Tot" orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____28856,FStar_Syntax_Syntax.Comp uu____28857) ->
                     let uu____28866 =
                       let uu___3754_28869 = problem  in
                       let uu____28872 =
                         let uu____28873 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____28873
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3754_28869.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____28872;
                         FStar_TypeChecker_Common.relation =
                           (uu___3754_28869.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3754_28869.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3754_28869.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3754_28869.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3754_28869.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3754_28869.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3754_28869.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3754_28869.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____28866 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____28874,FStar_Syntax_Syntax.Comp uu____28875) ->
                     let uu____28884 =
                       let uu___3754_28887 = problem  in
                       let uu____28890 =
                         let uu____28891 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____28891
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3754_28887.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____28890;
                         FStar_TypeChecker_Common.relation =
                           (uu___3754_28887.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3754_28887.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3754_28887.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3754_28887.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3754_28887.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3754_28887.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3754_28887.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3754_28887.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____28884 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____28892,FStar_Syntax_Syntax.GTotal uu____28893) ->
                     let uu____28902 =
                       let uu___3766_28905 = problem  in
                       let uu____28908 =
                         let uu____28909 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____28909
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3766_28905.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3766_28905.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3766_28905.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____28908;
                         FStar_TypeChecker_Common.element =
                           (uu___3766_28905.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3766_28905.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3766_28905.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3766_28905.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3766_28905.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3766_28905.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____28902 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____28910,FStar_Syntax_Syntax.Total uu____28911) ->
                     let uu____28920 =
                       let uu___3766_28923 = problem  in
                       let uu____28926 =
                         let uu____28927 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____28927
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3766_28923.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3766_28923.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3766_28923.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____28926;
                         FStar_TypeChecker_Common.element =
                           (uu___3766_28923.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3766_28923.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3766_28923.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3766_28923.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3766_28923.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3766_28923.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____28920 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____28928,FStar_Syntax_Syntax.Comp uu____28929) ->
                     let uu____28930 =
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
                     if uu____28930
                     then
                       let uu____28933 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____28933 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____28940 =
                            let uu____28945 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____28945
                            then (c1_comp, c2_comp)
                            else
                              (let uu____28954 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____28955 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____28954, uu____28955))
                             in
                          match uu____28940 with
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
                           (let uu____28963 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____28963
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____28971 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____28971 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____28974 =
                                  let uu____28976 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____28978 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____28976 uu____28978
                                   in
                                giveup env uu____28974 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____28989 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____28989 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29039 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29039 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29064 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29095  ->
                match uu____29095 with
                | (u1,u2) ->
                    let uu____29103 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29105 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29103 uu____29105))
         in
      FStar_All.pipe_right uu____29064 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29142,[])) when
          let uu____29169 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29169 -> "{}"
      | uu____29172 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29199 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29199
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____29211 =
              FStar_List.map
                (fun uu____29224  ->
                   match uu____29224 with
                   | (uu____29231,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Common.deferred
               in
            FStar_All.pipe_right uu____29211 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____29242 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____29242 imps
  
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
                  let uu____29299 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____29299
                  then
                    let uu____29307 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____29309 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____29307
                      (rel_to_string rel) uu____29309
                  else "TOP"  in
                let uu____29315 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____29315 with
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
              let uu____29375 =
                let uu____29378 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _29381  -> FStar_Pervasives_Native.Some _29381)
                  uu____29378
                 in
              FStar_Syntax_Syntax.new_bv uu____29375 t1  in
            let uu____29382 =
              let uu____29387 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____29387
               in
            match uu____29382 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____29447 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____29447
         then
           let uu____29452 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____29452
         else ());
        (let uu____29459 =
           FStar_Util.record_time (fun uu____29466  -> solve env probs)  in
         match uu____29459 with
         | (sol,ms) ->
             ((let uu____29478 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____29478
               then
                 let uu____29483 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____29483
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____29496 =
                     FStar_Util.record_time
                       (fun uu____29503  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____29496 with
                    | ((),ms1) ->
                        ((let uu____29514 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____29514
                          then
                            let uu____29519 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____29519
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____29533 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____29533
                     then
                       let uu____29540 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____29540
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
          ((let uu____29567 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____29567
            then
              let uu____29572 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____29572
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____29579 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____29579
             then
               let uu____29584 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____29584
             else ());
            (let f2 =
               let uu____29590 =
                 let uu____29591 = FStar_Syntax_Util.unmeta f1  in
                 uu____29591.FStar_Syntax_Syntax.n  in
               match uu____29590 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____29595 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3882_29596 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred =
                 (uu___3882_29596.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___3882_29596.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___3882_29596.FStar_TypeChecker_Common.implicits)
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
            let uu____29639 =
              let uu____29640 =
                let uu____29641 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _29642  ->
                       FStar_TypeChecker_Common.NonTrivial _29642)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____29641;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____29640  in
            FStar_All.pipe_left
              (fun _29649  -> FStar_Pervasives_Native.Some _29649)
              uu____29639
  
let with_guard_no_simp :
  'Auu____29659 .
    'Auu____29659 ->
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
            let uu____29682 =
              let uu____29683 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _29684  -> FStar_TypeChecker_Common.NonTrivial _29684)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____29683;
                FStar_TypeChecker_Common.deferred = d;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____29682
  
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
          (let uu____29717 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____29717
           then
             let uu____29722 = FStar_Syntax_Print.term_to_string t1  in
             let uu____29724 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____29722
               uu____29724
           else ());
          (let uu____29729 =
             let uu____29734 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____29734
              in
           match uu____29729 with
           | (prob,wl) ->
               let g =
                 let uu____29742 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____29750  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____29742  in
               ((let uu____29769 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____29769
                 then
                   let uu____29774 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____29774
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
        let uu____29795 = try_teq true env t1 t2  in
        match uu____29795 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____29800 = FStar_TypeChecker_Env.get_range env  in
              let uu____29801 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____29800 uu____29801);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____29809 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____29809
              then
                let uu____29814 = FStar_Syntax_Print.term_to_string t1  in
                let uu____29816 = FStar_Syntax_Print.term_to_string t2  in
                let uu____29818 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____29814
                  uu____29816 uu____29818
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
          let uu____29844 = FStar_TypeChecker_Env.get_range env  in
          let uu____29845 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____29844 uu____29845
  
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
        (let uu____29874 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____29874
         then
           let uu____29879 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____29881 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____29879 uu____29881
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____29892 =
           let uu____29899 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____29899 "sub_comp"
            in
         match uu____29892 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____29912 =
                 FStar_Util.record_time
                   (fun uu____29924  ->
                      let uu____29925 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____29934  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____29925)
                  in
               match uu____29912 with
               | (r,ms) ->
                   ((let uu____29963 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____29963
                     then
                       let uu____29968 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____29970 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____29972 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____29968 uu____29970
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____29972
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
      fun uu____30010  ->
        match uu____30010 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____30053 =
                 let uu____30059 =
                   let uu____30061 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____30063 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____30061 uu____30063
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____30059)  in
               let uu____30067 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____30053 uu____30067)
               in
            let equiv1 v1 v' =
              let uu____30080 =
                let uu____30085 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____30086 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____30085, uu____30086)  in
              match uu____30080 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____30106 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____30137 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____30137 with
                      | FStar_Syntax_Syntax.U_unif uu____30144 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____30173  ->
                                    match uu____30173 with
                                    | (u,v') ->
                                        let uu____30182 = equiv1 v1 v'  in
                                        if uu____30182
                                        then
                                          let uu____30187 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____30187 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____30208 -> []))
               in
            let uu____30213 =
              let wl =
                let uu___3975_30217 = empty_worklist env  in
                {
                  attempting = (uu___3975_30217.attempting);
                  wl_deferred = (uu___3975_30217.wl_deferred);
                  ctr = (uu___3975_30217.ctr);
                  defer_ok = false;
                  smt_ok = (uu___3975_30217.smt_ok);
                  umax_heuristic_ok = (uu___3975_30217.umax_heuristic_ok);
                  tcenv = (uu___3975_30217.tcenv);
                  wl_implicits = (uu___3975_30217.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____30236  ->
                      match uu____30236 with
                      | (lb,v1) ->
                          let uu____30243 =
                            solve_universe_eq (~- Prims.int_one) wl lb v1  in
                          (match uu____30243 with
                           | USolved wl1 -> ()
                           | uu____30246 -> fail1 lb v1)))
               in
            let rec check_ineq uu____30257 =
              match uu____30257 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____30269) -> true
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
                      uu____30293,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____30295,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____30306) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____30314,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____30323 -> false)
               in
            let uu____30329 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____30346  ->
                      match uu____30346 with
                      | (u,v1) ->
                          let uu____30354 = check_ineq (u, v1)  in
                          if uu____30354
                          then true
                          else
                            ((let uu____30362 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____30362
                              then
                                let uu____30367 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____30369 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____30367
                                  uu____30369
                              else ());
                             false)))
               in
            if uu____30329
            then ()
            else
              ((let uu____30379 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____30379
                then
                  ((let uu____30385 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____30385);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____30397 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____30397))
                else ());
               (let uu____30410 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____30410))
  
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
        let fail1 uu____30484 =
          match uu____30484 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4052_30510 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4052_30510.attempting);
            wl_deferred = (uu___4052_30510.wl_deferred);
            ctr = (uu___4052_30510.ctr);
            defer_ok;
            smt_ok = (uu___4052_30510.smt_ok);
            umax_heuristic_ok = (uu___4052_30510.umax_heuristic_ok);
            tcenv = (uu___4052_30510.tcenv);
            wl_implicits = (uu___4052_30510.wl_implicits)
          }  in
        (let uu____30513 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30513
         then
           let uu____30518 = FStar_Util.string_of_bool defer_ok  in
           let uu____30520 = wl_to_string wl  in
           let uu____30522 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Common.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____30518 uu____30520 uu____30522
         else ());
        (let g1 =
           let uu____30528 = solve_and_commit env wl fail1  in
           match uu____30528 with
           | FStar_Pervasives_Native.Some
               (uu____30535::uu____30536,uu____30537) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4067_30566 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4067_30566.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4067_30566.FStar_TypeChecker_Common.univ_ineqs);
                 FStar_TypeChecker_Common.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Common.implicits
                      imps)
               }
           | uu____30567 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env
           g1.FStar_TypeChecker_Common.univ_ineqs;
         (let uu___4072_30576 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4072_30576.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4072_30576.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4072_30576.FStar_TypeChecker_Common.implicits)
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
            let uu___4084_30653 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Common.deferred =
                (uu___4084_30653.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4084_30653.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___4084_30653.FStar_TypeChecker_Common.implicits)
            }  in
          let uu____30654 =
            let uu____30656 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____30656  in
          if uu____30654
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Common.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____30668 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____30669 =
                       let uu____30671 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____30671
                        in
                     FStar_Errors.diag uu____30668 uu____30669)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____30679 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____30680 =
                        let uu____30682 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____30682
                         in
                      FStar_Errors.diag uu____30679 uu____30680)
                   else ();
                   (let uu____30688 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____30688
                      "discharge_guard'" env vc1);
                   (let uu____30690 =
                      FStar_TypeChecker_Common.check_trivial vc1  in
                    match uu____30690 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____30699 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____30700 =
                                let uu____30702 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____30702
                                 in
                              FStar_Errors.diag uu____30699 uu____30700)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____30712 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____30713 =
                                let uu____30715 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____30715
                                 in
                              FStar_Errors.diag uu____30712 uu____30713)
                           else ();
                           (let vcs =
                              let uu____30729 = FStar_Options.use_tactics ()
                                 in
                              if uu____30729
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____30751  ->
                                     (let uu____30753 =
                                        FStar_Options.set_options
                                          "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____30753);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____30797  ->
                                              match uu____30797 with
                                              | (env1,goal,opts) ->
                                                  let uu____30813 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____30813, opts)))))
                              else
                                (let uu____30816 =
                                   let uu____30823 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____30823)  in
                                 [uu____30816])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____30856  ->
                                    match uu____30856 with
                                    | (env1,goal,opts) ->
                                        let uu____30866 =
                                          FStar_TypeChecker_Common.check_trivial
                                            goal
                                           in
                                        (match uu____30866 with
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
                                                (let uu____30877 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____30878 =
                                                   let uu____30880 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____30882 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____30880 uu____30882
                                                    in
                                                 FStar_Errors.diag
                                                   uu____30877 uu____30878)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____30889 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____30890 =
                                                   let uu____30892 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____30892
                                                    in
                                                 FStar_Errors.diag
                                                   uu____30889 uu____30890)
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
      let uu____30910 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____30910 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____30919 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____30919
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____30933 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____30933 with
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
        let uu____30963 = try_teq false env t1 t2  in
        match uu____30963 with
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
            let uu____31007 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____31007 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____31020 ->
                     let uu____31033 =
                       let uu____31034 = FStar_Syntax_Subst.compress r  in
                       uu____31034.FStar_Syntax_Syntax.n  in
                     (match uu____31033 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____31039) ->
                          unresolved ctx_u'
                      | uu____31056 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____31080 = acc  in
            match uu____31080 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____31099 = hd1  in
                     (match uu____31099 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____31110 = unresolved ctx_u  in
                             if uu____31110
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____31134 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____31134
                                     then
                                       let uu____31138 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____31138
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____31147 = teq_nosmt env1 t tm
                                          in
                                       match uu____31147 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4196_31157 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4196_31157.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4196_31157.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4196_31157.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4196_31157.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4196_31157.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4196_31157.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4196_31157.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4199_31165 = hd1  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4199_31165.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4199_31165.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4199_31165.FStar_TypeChecker_Common.imp_range)
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
                                    let uu___4203_31176 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4203_31176.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4203_31176.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4203_31176.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4203_31176.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4203_31176.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4203_31176.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4203_31176.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4203_31176.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4203_31176.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___4203_31176.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4203_31176.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4203_31176.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4203_31176.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4203_31176.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4203_31176.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4203_31176.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4203_31176.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4203_31176.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4203_31176.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4203_31176.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4203_31176.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4203_31176.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4203_31176.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4203_31176.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4203_31176.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4203_31176.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4203_31176.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4203_31176.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4203_31176.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4203_31176.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4203_31176.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4203_31176.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4203_31176.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4203_31176.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
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
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4203_31176.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4203_31176.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4203_31176.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4203_31176.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4203_31176.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4203_31176.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4203_31176.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
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
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4208_31180 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4208_31180.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4208_31180.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4208_31180.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4208_31180.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4208_31180.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4208_31180.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4208_31180.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4208_31180.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4208_31180.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4208_31180.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___4208_31180.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4208_31180.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4208_31180.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4208_31180.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4208_31180.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4208_31180.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4208_31180.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4208_31180.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4208_31180.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4208_31180.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4208_31180.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4208_31180.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4208_31180.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4208_31180.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4208_31180.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4208_31180.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4208_31180.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4208_31180.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4208_31180.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4208_31180.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4208_31180.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4208_31180.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4208_31180.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4208_31180.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
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
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4208_31180.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4208_31180.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4208_31180.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4208_31180.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4208_31180.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4208_31180.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4208_31180.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
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
                                      }
                                    else env1  in
                                  (let uu____31185 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____31185
                                   then
                                     let uu____31190 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____31192 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____31194 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____31196 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____31190 uu____31192 uu____31194
                                       reason uu____31196
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4214_31203  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____31210 =
                                             let uu____31220 =
                                               let uu____31228 =
                                                 let uu____31230 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____31232 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____31234 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____31230 uu____31232
                                                   uu____31234
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____31228, r)
                                                in
                                             [uu____31220]  in
                                           FStar_Errors.add_errors
                                             uu____31210);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___4222_31254 = g1  in
                                       {
                                         FStar_TypeChecker_Common.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Common.deferred =
                                           (uu___4222_31254.FStar_TypeChecker_Common.deferred);
                                         FStar_TypeChecker_Common.univ_ineqs
                                           =
                                           (uu___4222_31254.FStar_TypeChecker_Common.univ_ineqs);
                                         FStar_TypeChecker_Common.implicits =
                                           (uu___4222_31254.FStar_TypeChecker_Common.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____31258 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____31269  ->
                                               let uu____31270 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____31272 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____31274 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____31270 uu____31272
                                                 reason uu____31274)) env2 g2
                                         true
                                        in
                                     match uu____31258 with
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
          let uu___4230_31282 = g  in
          let uu____31283 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4230_31282.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4230_31282.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4230_31282.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____31283
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
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
<<<<<<< HEAD
              let uu____30464 =
=======
              let uu____29750 =
>>>>>>> snap
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
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
            FStar_TypeChecker_Env.lookup_attr env
              FStar_Parser_Const.resolve_implicits_attr_string
             in
          (match uu____31329 with
           | {
               FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                 (uu____31332,lid::[]);
               FStar_Syntax_Syntax.sigrng = uu____31334;
               FStar_Syntax_Syntax.sigquals = uu____31335;
               FStar_Syntax_Syntax.sigmeta = uu____31336;
               FStar_Syntax_Syntax.sigattrs = uu____31337;_}::uu____31338 ->
               let qn = FStar_TypeChecker_Env.lookup_qname env lid  in
               let fv =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   (FStar_Syntax_Syntax.Delta_constant_at_level
                      Prims.int_zero) FStar_Pervasives_Native.None
                  in
               let dd =
                 let uu____31351 =
                   FStar_TypeChecker_Env.delta_depth_of_qninfo fv qn  in
                 match uu____31351 with
                 | FStar_Pervasives_Native.Some dd -> dd
                 | FStar_Pervasives_Native.None  -> failwith "Expected a dd"
                  in
               let term =
                 let uu____31357 =
                   FStar_Syntax_Syntax.lid_as_fv lid dd
                     FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____31357  in
               (env.FStar_TypeChecker_Env.try_solve_implicits_hook env term
                  g1.FStar_TypeChecker_Common.implicits;
                (let uu____31359 = discharge_guard env g1  in
                 FStar_All.pipe_left (fun a3  -> ()) uu____31359))
           | uu____31360 ->
               let uu____31363 =
                 let uu____31369 =
                   let uu____31371 =
                     FStar_Syntax_Print.uvar_to_string
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   let uu____31373 =
                     FStar_TypeChecker_Normalize.term_to_string env
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                      in
                   FStar_Util.format3
                     "Failed to resolve implicit argument %s of type %s introduced for %s"
                     uu____31371 uu____31373
                     imp.FStar_TypeChecker_Common.imp_reason
                    in
                 (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                   uu____31369)
                  in
               FStar_Errors.raise_error uu____31363
                 imp.FStar_TypeChecker_Common.imp_range)
>>>>>>> snap
=======
                uu____29748 uu____29750 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____29746)
             in
          FStar_Errors.raise_error uu____29740
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
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4273_31414.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred =
          (uu___4273_31414.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
          (uu___4266_31500.FStar_TypeChecker_Common.implicits)
<<<<<<< HEAD
>>>>>>> snap
=======
      let uu___4074_29791 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___4074_29791.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___4074_29791.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
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
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31450
         then
           let uu____31455 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31457 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____31455
             uu____31457
         else ());
        (let uu____31462 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31462 with
         | (prob,x,wl) ->
             let g =
               let uu____31481 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____31490  -> FStar_Pervasives_Native.None)
                  in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
               FStar_All.pipe_left (with_guard env prob) uu____31567  in
             ((let uu____31595 =
>>>>>>> snap
=======
        (let uu____29827 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____29827
         then
           let uu____29832 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____29834 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____29832
             uu____29834
         else ());
        (let uu____29839 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____29839 with
         | (prob,x,wl) ->
             let g =
               let uu____29858 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____29869  -> FStar_Pervasives_Native.None)
                  in
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
               then
                 let uu____29895 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____29897 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____29899 =
                   let uu____29901 = FStar_Util.must g  in
                   guard_to_string env uu____29901  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
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
               then
                 let uu____31514 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____31516 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____31518 =
                   let uu____31520 = FStar_Util.must g  in
                   guard_to_string env uu____31520  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
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
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30036
         then
           let uu____30041 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____30043 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____30041
             uu____30043
         else ());
        (let uu____30048 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____30048 with
         | (prob,x,wl) ->
             let g =
               let uu____30063 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____30074  -> FStar_Pervasives_Native.None)
                  in
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
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31655
         then
           let uu____31660 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31662 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____31660
             uu____31662
         else ());
        (let uu____31667 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31667 with
         | (prob,x,wl) ->
             let g =
               let uu____31682 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____31691  -> FStar_Pervasives_Native.None)
                  in
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
                    let uu____31666 =
                      let uu____31667 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____31667]  in
                    FStar_TypeChecker_Env.close_guard env uu____31666 g1  in
>>>>>>> snap
=======
                    let uu____31713 =
                      let uu____31714 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____31714]  in
                    FStar_TypeChecker_Env.close_guard env uu____31713 g1  in
>>>>>>> cp debugging an issue
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
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  