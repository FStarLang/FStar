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
  wl_implicits: FStar_TypeChecker_Env.implicits }
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
  worklist -> FStar_TypeChecker_Env.implicits) =
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
                       FStar_TypeChecker_Env.imp_reason = reason;
                       FStar_TypeChecker_Env.imp_uvar = ctx_uvar;
                       FStar_TypeChecker_Env.imp_tm = t;
                       FStar_TypeChecker_Env.imp_range = r
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
  FStar_TypeChecker_Env.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * Prims.string) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____614 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits))
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
                        FStar_Syntax_Syntax.delta_constant] env
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
            (let uu____8115 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8115
             then
               let uu____8120 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8122 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8124 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8120
                 uu____8122 uu____8124
             else ());
            (let maybe_normalize_refinement steps env1 t =
               let uu____8151 = FStar_Syntax_Util.head_and_args t  in
               match uu____8151 with
               | (head1,uu____8171) ->
                   let t' = normalize_refinement steps env1 t  in
                   let uu____8197 = FStar_Syntax_Util.head_and_args t'  in
                   (match uu____8197 with
                    | (head',uu____8217) ->
                        let uu____8242 = head_matches env1 head1 head'  in
                        (match uu____8242 with
                         | FullMatch  -> FStar_Pervasives_Native.None
                         | HeadMatch uu____8245 ->
                             FStar_Pervasives_Native.None
                         | uu____8247 -> FStar_Pervasives_Native.Some t'))
                in
             let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8275 =
                 if d1_greater_than_d2
                 then
                   let t1' =
                     maybe_normalize_refinement
                       [FStar_TypeChecker_Env.UnfoldUntil d2;
                       FStar_TypeChecker_Env.Weak;
                       FStar_TypeChecker_Env.HNF] env t11
                      in
                   (t1', (FStar_Pervasives_Native.Some t21))
                 else
                   (let t2' =
                      maybe_normalize_refinement
                        [FStar_TypeChecker_Env.UnfoldUntil d1;
                        FStar_TypeChecker_Env.Weak;
                        FStar_TypeChecker_Env.HNF] env t21
                       in
                    ((FStar_Pervasives_Native.Some t11), t2'))
                  in
               match uu____8275 with
               | (t1',t2') ->
                   (match (t1', t2') with
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.Some t22) ->
                        aux retry (n_delta + Prims.int_one) t12 t22
                    | uu____8402 -> fail1 n_delta r t11 t21)
                in
             let reduce_both_and_try_again d r1 =
               let uu____8440 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8440 with
               | FStar_Pervasives_Native.None  -> fail1 n_delta r1 t11 t21
               | FStar_Pervasives_Native.Some d1 ->
                   let t1' =
                     maybe_normalize_refinement
                       [FStar_TypeChecker_Env.UnfoldUntil d1;
                       FStar_TypeChecker_Env.Weak;
                       FStar_TypeChecker_Env.HNF] env t11
                      in
                   let t2' =
                     maybe_normalize_refinement
                       [FStar_TypeChecker_Env.UnfoldUntil d1;
                       FStar_TypeChecker_Env.Weak;
                       FStar_TypeChecker_Env.HNF] env t21
                      in
                   (match (t1', t2') with
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.Some t22) ->
                        aux retry (n_delta + Prims.int_one) t12 t22
                    | uu____8489 -> fail1 n_delta r1 t11 t21)
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
                  uu____8523),uu____8524)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8549 =
                      let uu____8558 = maybe_inline t11  in
                      let uu____8561 = maybe_inline t21  in
                      (uu____8558, uu____8561)  in
                    match uu____8549 with
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
                 (uu____8608,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8609))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8634 =
                      let uu____8643 = maybe_inline t11  in
                      let uu____8646 = maybe_inline t21  in
                      (uu____8643, uu____8646)  in
                    match uu____8634 with
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
             | MisMatch uu____8705 -> fail1 n_delta r t11 t21
             | uu____8714 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8733 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8733
           then
             let uu____8738 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8740 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8742 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8754 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8779 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8779
                    (fun uu____8818  ->
                       match uu____8818 with
                       | (t11,t21) ->
                           let uu____8826 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8828 =
                             let uu____8830 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____8830  in
                           Prims.op_Hat uu____8826 uu____8828))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8738 uu____8740 uu____8742 uu____8754
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____8847 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____8847 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___24_8862  ->
    match uu___24_8862 with
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
      let uu___1231_8911 = p  in
      let uu____8914 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8915 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1231_8911.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8914;
        FStar_TypeChecker_Common.relation =
          (uu___1231_8911.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8915;
        FStar_TypeChecker_Common.element =
          (uu___1231_8911.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1231_8911.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1231_8911.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1231_8911.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1231_8911.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1231_8911.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8930 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____8930
            (fun _8935  -> FStar_TypeChecker_Common.TProb _8935)
      | FStar_TypeChecker_Common.CProb uu____8936 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____8959 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____8959 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8967 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8967 with
           | (lh,lhs_args) ->
               let uu____9014 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____9014 with
                | (rh,rhs_args) ->
                    let uu____9061 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9074,FStar_Syntax_Syntax.Tm_uvar uu____9075)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____9164 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9191,uu____9192)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____9207,FStar_Syntax_Syntax.Tm_uvar uu____9208)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9223,FStar_Syntax_Syntax.Tm_arrow uu____9224)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1282_9254 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1282_9254.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1282_9254.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1282_9254.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1282_9254.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1282_9254.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1282_9254.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1282_9254.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1282_9254.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1282_9254.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9257,FStar_Syntax_Syntax.Tm_type uu____9258)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1282_9274 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1282_9274.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1282_9274.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1282_9274.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1282_9274.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1282_9274.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1282_9274.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1282_9274.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1282_9274.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1282_9274.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____9277,FStar_Syntax_Syntax.Tm_uvar uu____9278)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1282_9294 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1282_9294.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1282_9294.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1282_9294.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1282_9294.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1282_9294.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1282_9294.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1282_9294.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1282_9294.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1282_9294.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9297,FStar_Syntax_Syntax.Tm_uvar uu____9298)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9313,uu____9314)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9329,FStar_Syntax_Syntax.Tm_uvar uu____9330)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9345,uu____9346) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____9061 with
                     | (rank,tp1) ->
                         let uu____9359 =
                           FStar_All.pipe_right
                             (let uu___1302_9363 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1302_9363.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1302_9363.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1302_9363.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1302_9363.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1302_9363.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1302_9363.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1302_9363.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1302_9363.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1302_9363.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _9366  ->
                                FStar_TypeChecker_Common.TProb _9366)
                            in
                         (rank, uu____9359))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9370 =
            FStar_All.pipe_right
              (let uu___1306_9374 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1306_9374.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1306_9374.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1306_9374.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1306_9374.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1306_9374.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1306_9374.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1306_9374.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1306_9374.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1306_9374.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _9377  -> FStar_TypeChecker_Common.CProb _9377)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9370)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9437 probs =
      match uu____9437 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9518 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____9539 = rank wl.tcenv hd1  in
               (match uu____9539 with
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
                      (let uu____9600 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9605 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9605)
                          in
                       if uu____9600
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
          let uu____9678 = FStar_Syntax_Util.head_and_args t  in
          match uu____9678 with
          | (hd1,uu____9697) ->
              let uu____9722 =
                let uu____9723 = FStar_Syntax_Subst.compress hd1  in
                uu____9723.FStar_Syntax_Syntax.n  in
              (match uu____9722 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9728) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9763  ->
                           match uu____9763 with
                           | (y,uu____9772) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9795  ->
                                       match uu____9795 with
                                       | (x,uu____9804) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9809 -> false)
           in
        let uu____9811 = rank tcenv p  in
        match uu____9811 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9820 -> true
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
    match projectee with | UDeferred _0 -> true | uu____9857 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9876 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9896 -> false
  
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
                        let uu____9958 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9958 with
                        | (k,uu____9966) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9979 -> false)))
            | uu____9981 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____10033 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____10041 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____10041 = Prims.int_zero))
                           in
                        if uu____10033 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____10062 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____10070 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____10070 = Prims.int_zero))
                      in
                   Prims.op_Negation uu____10062)
               in
            let uu____10074 = filter1 u12  in
            let uu____10077 = filter1 u22  in (uu____10074, uu____10077)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then UFailed "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____10112 = filter_out_common_univs us1 us2  in
                   (match uu____10112 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____10172 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____10172 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____10175 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          (let uu____10186 =
                             let uu____10188 =
                               FStar_Syntax_Print.univ_to_string u12  in
                             let uu____10190 =
                               FStar_Syntax_Print.univ_to_string u22  in
                             FStar_Util.format2
                               "Unable to unify universes: %s and %s"
                               uu____10188 uu____10190
                              in
                           UFailed uu____10186))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10216 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10216 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10242 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10242 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10245 ->
                   let uu____10250 =
                     let uu____10252 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____10254 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format3
                       "Unable to unify universes: %s and %s (%s)"
                       uu____10252 uu____10254 msg
                      in
                   UFailed uu____10250)
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10257,uu____10258) ->
              let uu____10260 =
                let uu____10262 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10264 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10262 uu____10264
                 in
              failwith uu____10260
          | (FStar_Syntax_Syntax.U_unknown ,uu____10267) ->
              let uu____10268 =
                let uu____10270 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10272 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10270 uu____10272
                 in
              failwith uu____10268
          | (uu____10275,FStar_Syntax_Syntax.U_bvar uu____10276) ->
              let uu____10278 =
                let uu____10280 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10282 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10280 uu____10282
                 in
              failwith uu____10278
          | (uu____10285,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10286 =
                let uu____10288 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10290 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10288 uu____10290
                 in
              failwith uu____10286
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10320 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10320
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10337 = occurs_univ v1 u3  in
              if uu____10337
              then
                let uu____10340 =
                  let uu____10342 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10344 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10342 uu____10344
                   in
                try_umax_components u11 u21 uu____10340
              else
                (let uu____10349 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10349)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10361 = occurs_univ v1 u3  in
              if uu____10361
              then
                let uu____10364 =
                  let uu____10366 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10368 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10366 uu____10368
                   in
                try_umax_components u11 u21 uu____10364
              else
                (let uu____10373 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10373)
          | (FStar_Syntax_Syntax.U_max uu____10374,uu____10375) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10383 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10383
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10389,FStar_Syntax_Syntax.U_max uu____10390) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10398 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10398
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10404,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10406,FStar_Syntax_Syntax.U_name uu____10407) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10409) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10411) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10413,FStar_Syntax_Syntax.U_succ uu____10414) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10416,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10523 = bc1  in
      match uu____10523 with
      | (bs1,mk_cod1) ->
          let uu____10567 = bc2  in
          (match uu____10567 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10678 = aux xs ys  in
                     (match uu____10678 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10761 =
                       let uu____10768 = mk_cod1 xs  in ([], uu____10768)  in
                     let uu____10771 =
                       let uu____10778 = mk_cod2 ys  in ([], uu____10778)  in
                     (uu____10761, uu____10771)
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
                  let uu____10847 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10847 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____10850 =
                    let uu____10851 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____10851 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____10850
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____10856 = has_type_guard t1 t2  in (uu____10856, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____10857 = has_type_guard t2 t1  in (uu____10857, wl)
  
let is_flex_pat :
  'Auu____10867 'Auu____10868 'Auu____10869 .
    ('Auu____10867 * 'Auu____10868 * 'Auu____10869 Prims.list) -> Prims.bool
  =
  fun uu___25_10883  ->
    match uu___25_10883 with
    | (uu____10892,uu____10893,[]) -> true
    | uu____10897 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____10930 = f  in
      match uu____10930 with
      | (uu____10937,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____10938;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10939;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____10942;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____10943;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____10944;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____10945;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____11015  ->
                 match uu____11015 with
                 | (y,uu____11024) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____11178 =
                  let uu____11193 =
                    let uu____11196 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11196  in
                  ((FStar_List.rev pat_binders), uu____11193)  in
                FStar_Pervasives_Native.Some uu____11178
            | (uu____11229,[]) ->
                let uu____11260 =
                  let uu____11275 =
                    let uu____11278 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11278  in
                  ((FStar_List.rev pat_binders), uu____11275)  in
                FStar_Pervasives_Native.Some uu____11260
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11369 =
                  let uu____11370 = FStar_Syntax_Subst.compress a  in
                  uu____11370.FStar_Syntax_Syntax.n  in
                (match uu____11369 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11390 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11390
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1630_11420 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1630_11420.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1630_11420.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____11424 =
                            let uu____11425 =
                              let uu____11432 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11432)  in
                            FStar_Syntax_Syntax.NT uu____11425  in
                          [uu____11424]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___1636_11448 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1636_11448.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1636_11448.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11449 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11489 =
                  let uu____11504 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11504  in
                (match uu____11489 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11579 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11612 ->
               let uu____11613 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11613 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____11935 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____11935
       then
         let uu____11940 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11940
       else ());
      (let uu____11945 = next_prob probs  in
       match uu____11945 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___1661_11972 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___1661_11972.wl_deferred);
               ctr = (uu___1661_11972.ctr);
               defer_ok = (uu___1661_11972.defer_ok);
               smt_ok = (uu___1661_11972.smt_ok);
               umax_heuristic_ok = (uu___1661_11972.umax_heuristic_ok);
               tcenv = (uu___1661_11972.tcenv);
               wl_implicits = (uu___1661_11972.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11981 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____11981
                 then
                   let uu____11984 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____11984
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
                           (let uu___1673_11996 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1673_11996.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1673_11996.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1673_11996.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1673_11996.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1673_11996.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1673_11996.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1673_11996.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1673_11996.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1673_11996.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____12022 ->
                let uu____12033 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____12104  ->
                          match uu____12104 with
                          | (c,uu____12115,uu____12116) -> c < probs.ctr))
                   in
                (match uu____12033 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____12171 =
                            let uu____12176 =
                              FStar_List.map
                                (fun uu____12194  ->
                                   match uu____12194 with
                                   | (uu____12208,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____12176, (probs.wl_implicits))  in
                          Success uu____12171
                      | uu____12216 ->
                          let uu____12227 =
                            let uu___1691_12228 = probs  in
                            let uu____12229 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____12252  ->
                                      match uu____12252 with
                                      | (uu____12261,uu____12262,y) -> y))
                               in
                            {
                              attempting = uu____12229;
                              wl_deferred = rest;
                              ctr = (uu___1691_12228.ctr);
                              defer_ok = (uu___1691_12228.defer_ok);
                              smt_ok = (uu___1691_12228.smt_ok);
                              umax_heuristic_ok =
                                (uu___1691_12228.umax_heuristic_ok);
                              tcenv = (uu___1691_12228.tcenv);
                              wl_implicits = (uu___1691_12228.wl_implicits)
                            }  in
                          solve env uu____12227))))

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
            let uu____12273 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____12273 with
            | USolved wl1 ->
                let uu____12275 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____12275
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
                  let uu____12329 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12329 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12332 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12345;
                  FStar_Syntax_Syntax.vars = uu____12346;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12349;
                  FStar_Syntax_Syntax.vars = uu____12350;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12363,uu____12364) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12372,FStar_Syntax_Syntax.Tm_uinst uu____12373) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12381 -> USolved wl

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
            ((let uu____12393 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12393
              then
                let uu____12398 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12398 msg
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
               let uu____12490 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12490 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12545 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12545
                then
                  let uu____12550 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12552 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12550 uu____12552
                else ());
               (let uu____12557 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12557 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12603 = eq_prob t1 t2 wl2  in
                         (match uu____12603 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12624 ->
                         let uu____12633 = eq_prob t1 t2 wl2  in
                         (match uu____12633 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____12683 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____12698 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____12699 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____12698, uu____12699)
                           | FStar_Pervasives_Native.None  ->
                               let uu____12704 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____12705 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____12704, uu____12705)
                            in
                         (match uu____12683 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12736 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____12736 with
                                | (t1_hd,t1_args) ->
                                    let uu____12781 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____12781 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12847 =
                                              let uu____12854 =
                                                let uu____12865 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____12865 :: t1_args  in
                                              let uu____12882 =
                                                let uu____12891 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____12891 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____12940  ->
                                                   fun uu____12941  ->
                                                     fun uu____12942  ->
                                                       match (uu____12940,
                                                               uu____12941,
                                                               uu____12942)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____12992),
                                                          (a2,uu____12994))
                                                           ->
                                                           let uu____13031 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____13031
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12854
                                                uu____12882
                                               in
                                            match uu____12847 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1845_13057 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___1845_13057.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1845_13057.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1845_13057.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13069 =
                                                  solve env1 wl'  in
                                                (match uu____13069 with
                                                 | Success (uu____13072,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___1854_13076
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___1854_13076.attempting);
                                                            wl_deferred =
                                                              (uu___1854_13076.wl_deferred);
                                                            ctr =
                                                              (uu___1854_13076.ctr);
                                                            defer_ok =
                                                              (uu___1854_13076.defer_ok);
                                                            smt_ok =
                                                              (uu___1854_13076.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___1854_13076.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___1854_13076.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____13077 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____13110 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____13110 with
                                | (t1_base,p1_opt) ->
                                    let uu____13146 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____13146 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____13245 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____13245
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
                                               let uu____13298 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____13298
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
                                               let uu____13330 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13330
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
                                               let uu____13362 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13362
                                           | uu____13365 -> t_base  in
                                         let uu____13382 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13382 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13396 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13396, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13403 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13403 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13439 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13439 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13475 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13475
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
                              let uu____13499 = combine t11 t21 wl2  in
                              (match uu____13499 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13532 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13532
                                     then
                                       let uu____13537 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13537
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13579 ts1 =
               match uu____13579 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13642 = pairwise out t wl2  in
                        (match uu____13642 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____13678 =
               let uu____13689 = FStar_List.hd ts  in (uu____13689, [], wl1)
                in
             let uu____13698 = FStar_List.tl ts  in
             aux uu____13678 uu____13698  in
           let uu____13705 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____13705 with
           | (this_flex,this_rigid) ->
               let uu____13731 =
                 let uu____13732 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____13732.FStar_Syntax_Syntax.n  in
               (match uu____13731 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____13757 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____13757
                    then
                      let uu____13760 = destruct_flex_t this_flex wl  in
                      (match uu____13760 with
                       | (flex,wl1) ->
                           let uu____13767 = quasi_pattern env flex  in
                           (match uu____13767 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____13786 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____13786
                                  then
                                    let uu____13791 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13791
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13798 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___1956_13801 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___1956_13801.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___1956_13801.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___1956_13801.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___1956_13801.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___1956_13801.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___1956_13801.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___1956_13801.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___1956_13801.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___1956_13801.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____13798)
                | uu____13802 ->
                    ((let uu____13804 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13804
                      then
                        let uu____13809 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13809
                      else ());
                     (let uu____13814 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____13814 with
                      | (u,_args) ->
                          let uu____13857 =
                            let uu____13858 = FStar_Syntax_Subst.compress u
                               in
                            uu____13858.FStar_Syntax_Syntax.n  in
                          (match uu____13857 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____13886 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____13886 with
                                 | (u',uu____13905) ->
                                     let uu____13930 =
                                       let uu____13931 = whnf env u'  in
                                       uu____13931.FStar_Syntax_Syntax.n  in
                                     (match uu____13930 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13953 -> false)
                                  in
                               let uu____13955 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___26_13978  ->
                                         match uu___26_13978 with
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
                                              | uu____13992 -> false)
                                         | uu____13996 -> false))
                                  in
                               (match uu____13955 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____14011 = whnf env this_rigid
                                         in
                                      let uu____14012 =
                                        FStar_List.collect
                                          (fun uu___27_14018  ->
                                             match uu___27_14018 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____14024 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____14024]
                                             | uu____14028 -> [])
                                          bounds_probs
                                         in
                                      uu____14011 :: uu____14012  in
                                    let uu____14029 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____14029 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____14062 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____14077 =
                                               let uu____14078 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____14078.FStar_Syntax_Syntax.n
                                                in
                                             match uu____14077 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____14090 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____14090)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____14101 -> bound  in
                                           let uu____14102 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____14102)  in
                                         (match uu____14062 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____14137 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____14137
                                                then
                                                  let wl'1 =
                                                    let uu___2016_14143 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2016_14143.wl_deferred);
                                                      ctr =
                                                        (uu___2016_14143.ctr);
                                                      defer_ok =
                                                        (uu___2016_14143.defer_ok);
                                                      smt_ok =
                                                        (uu___2016_14143.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2016_14143.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2016_14143.tcenv);
                                                      wl_implicits =
                                                        (uu___2016_14143.wl_implicits)
                                                    }  in
                                                  let uu____14144 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____14144
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____14150 =
                                                  solve_t env eq_prob
                                                    (let uu___2021_14152 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2021_14152.wl_deferred);
                                                       ctr =
                                                         (uu___2021_14152.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2021_14152.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2021_14152.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2021_14152.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____14150 with
                                                | Success (uu____14154,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2027_14157 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2027_14157.wl_deferred);
                                                        ctr =
                                                          (uu___2027_14157.ctr);
                                                        defer_ok =
                                                          (uu___2027_14157.defer_ok);
                                                        smt_ok =
                                                          (uu___2027_14157.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2027_14157.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2027_14157.tcenv);
                                                        wl_implicits =
                                                          (uu___2027_14157.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2030_14159 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2030_14159.attempting);
                                                        wl_deferred =
                                                          (uu___2030_14159.wl_deferred);
                                                        ctr =
                                                          (uu___2030_14159.ctr);
                                                        defer_ok =
                                                          (uu___2030_14159.defer_ok);
                                                        smt_ok =
                                                          (uu___2030_14159.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2030_14159.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2030_14159.tcenv);
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
                                                    let uu____14175 =
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
                                                    ((let uu____14189 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____14189
                                                      then
                                                        let uu____14194 =
                                                          let uu____14196 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____14196
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____14194
                                                      else ());
                                                     (let uu____14209 =
                                                        let uu____14224 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____14224)
                                                         in
                                                      match uu____14209 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____14246))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14272 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14272
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
                                                                  let uu____14292
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14292))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14317 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14317
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
                                                                    let uu____14337
                                                                    =
                                                                    let uu____14342
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14342
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14337
                                                                    [] wl2
                                                                     in
                                                                  let uu____14348
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14348))))
                                                      | uu____14349 ->
                                                          giveup env
                                                            (Prims.op_Hat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____14365 when flip ->
                               let uu____14366 =
                                 let uu____14368 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14370 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14368 uu____14370
                                  in
                               failwith uu____14366
                           | uu____14373 ->
                               let uu____14374 =
                                 let uu____14376 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14378 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14376 uu____14378
                                  in
                               failwith uu____14374)))))

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
                      (fun uu____14414  ->
                         match uu____14414 with
                         | (x,i) ->
                             let uu____14433 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14433, i)) bs_lhs
                     in
                  let uu____14436 = lhs  in
                  match uu____14436 with
                  | (uu____14437,u_lhs,uu____14439) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14536 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14546 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14546, univ)
                             in
                          match uu____14536 with
                          | (k,univ) ->
                              let uu____14553 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14553 with
                               | (uu____14570,u,wl3) ->
                                   let uu____14573 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14573, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14599 =
                              let uu____14612 =
                                let uu____14623 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14623 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____14674  ->
                                   fun uu____14675  ->
                                     match (uu____14674, uu____14675) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____14776 =
                                           let uu____14783 =
                                             let uu____14786 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____14786
                                              in
                                           copy_uvar u_lhs [] uu____14783 wl2
                                            in
                                         (match uu____14776 with
                                          | (uu____14815,t_a,wl3) ->
                                              let uu____14818 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____14818 with
                                               | (uu____14837,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14612
                                ([], wl1)
                               in
                            (match uu____14599 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2140_14893 = ct  in
                                   let uu____14894 =
                                     let uu____14897 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14897
                                      in
                                   let uu____14912 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2140_14893.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2140_14893.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14894;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14912;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2140_14893.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2143_14930 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2143_14930.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2143_14930.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14933 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____14933 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14995 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14995 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____15006 =
                                          let uu____15011 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____15011)  in
                                        TERM uu____15006  in
                                      let uu____15012 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____15012 with
                                       | (sub_prob,wl3) ->
                                           let uu____15026 =
                                             let uu____15027 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____15027
                                              in
                                           solve env uu____15026))
                             | (x,imp)::formals2 ->
                                 let uu____15049 =
                                   let uu____15056 =
                                     let uu____15059 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____15059
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____15056 wl1
                                    in
                                 (match uu____15049 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____15080 =
                                          let uu____15083 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____15083
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____15080 u_x
                                         in
                                      let uu____15084 =
                                        let uu____15087 =
                                          let uu____15090 =
                                            let uu____15091 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____15091, imp)  in
                                          [uu____15090]  in
                                        FStar_List.append bs_terms
                                          uu____15087
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____15084 formals2 wl2)
                              in
                           let uu____15118 = occurs_check u_lhs arrow1  in
                           (match uu____15118 with
                            | (uu____15131,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____15147 =
                                    let uu____15149 = FStar_Option.get msg
                                       in
                                    Prims.op_Hat "occurs-check failed: "
                                      uu____15149
                                     in
                                  giveup_or_defer env orig wl uu____15147
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
              (let uu____15182 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____15182
               then
                 let uu____15187 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____15190 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____15187 (rel_to_string (p_rel orig)) uu____15190
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15317 = rhs wl1 scope env1 subst1  in
                     (match uu____15317 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15338 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15338
                            then
                              let uu____15343 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15343
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15421 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15421 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2212_15423 = hd1  in
                       let uu____15424 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2212_15423.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2212_15423.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15424
                       }  in
                     let hd21 =
                       let uu___2215_15428 = hd2  in
                       let uu____15429 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2215_15428.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2215_15428.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15429
                       }  in
                     let uu____15432 =
                       let uu____15437 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15437
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15432 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____15458 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst1
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15458
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15465 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____15465 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15532 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15532
                                  in
                               ((let uu____15550 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15550
                                 then
                                   let uu____15555 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15557 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15555
                                     uu____15557
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____15590 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15626 = aux wl [] env [] bs1 bs2  in
               match uu____15626 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15681 = attempt sub_probs wl2  in
                   solve env uu____15681)

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
            let uu___2250_15702 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2250_15702.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2250_15702.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15715 = try_solve env wl'  in
          match uu____15715 with
          | Success (uu____15716,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2259_15720 = wl  in
                  {
                    attempting = (uu___2259_15720.attempting);
                    wl_deferred = (uu___2259_15720.wl_deferred);
                    ctr = (uu___2259_15720.ctr);
                    defer_ok = (uu___2259_15720.defer_ok);
                    smt_ok = (uu___2259_15720.smt_ok);
                    umax_heuristic_ok = (uu___2259_15720.umax_heuristic_ok);
                    tcenv = (uu___2259_15720.tcenv);
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
        (let uu____15732 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15732 wl)

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
              let uu____15746 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15746 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15780 = lhs1  in
              match uu____15780 with
              | (uu____15783,ctx_u,uu____15785) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15793 ->
                        let uu____15794 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15794 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15843 = quasi_pattern env1 lhs1  in
              match uu____15843 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15877) ->
                  let uu____15882 = lhs1  in
                  (match uu____15882 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15897 = occurs_check ctx_u rhs1  in
                       (match uu____15897 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15948 =
                                let uu____15956 =
                                  let uu____15958 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15958
                                   in
                                FStar_Util.Inl uu____15956  in
                              (uu____15948, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15986 =
                                 let uu____15988 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15988  in
                               if uu____15986
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____16015 =
                                    let uu____16023 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____16023  in
                                  let uu____16029 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____16015, uu____16029)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____16073 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____16073 with
              | (rhs_hd,args) ->
                  let uu____16116 = FStar_Util.prefix args  in
                  (match uu____16116 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____16188 = lhs1  in
                       (match uu____16188 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____16192 =
                              let uu____16203 =
                                let uu____16210 =
                                  let uu____16213 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____16213
                                   in
                                copy_uvar u_lhs [] uu____16210 wl1  in
                              match uu____16203 with
                              | (uu____16240,t_last_arg,wl2) ->
                                  let uu____16243 =
                                    let uu____16250 =
                                      let uu____16251 =
                                        let uu____16260 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____16260]  in
                                      FStar_List.append bs_lhs uu____16251
                                       in
                                    copy_uvar u_lhs uu____16250 t_res_lhs wl2
                                     in
                                  (match uu____16243 with
                                   | (uu____16295,lhs',wl3) ->
                                       let uu____16298 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____16298 with
                                        | (uu____16315,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____16192 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____16336 =
                                     let uu____16337 =
                                       let uu____16342 =
                                         let uu____16343 =
                                           let uu____16346 =
                                             let uu____16351 =
                                               let uu____16352 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____16352]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____16351
                                              in
                                           uu____16346
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____16343
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____16342)  in
                                     TERM uu____16337  in
                                   [uu____16336]  in
                                 let uu____16377 =
                                   let uu____16384 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____16384 with
                                   | (p1,wl3) ->
                                       let uu____16404 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____16404 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____16377 with
                                  | (sub_probs,wl3) ->
                                      let uu____16436 =
                                        let uu____16437 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____16437  in
                                      solve env1 uu____16436))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16471 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16471 with
                | (uu____16489,args) ->
                    (match args with | [] -> false | uu____16525 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16544 =
                  let uu____16545 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16545.FStar_Syntax_Syntax.n  in
                match uu____16544 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16549 -> true
                | uu____16565 -> false  in
              let uu____16567 = quasi_pattern env1 lhs1  in
              match uu____16567 with
              | FStar_Pervasives_Native.None  ->
                  let uu____16578 =
                    let uu____16580 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                      uu____16580
                     in
                  giveup_or_defer env1 orig1 wl1 uu____16578
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16589 = is_app rhs1  in
                  if uu____16589
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____16594 = is_arrow rhs1  in
                     if uu____16594
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____16599 =
                          let uu____16601 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heuristic cannot solve %s; rhs not an app or arrow"
                            uu____16601
                           in
                        giveup_or_defer env1 orig1 wl1 uu____16599))
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
                let uu____16612 = lhs  in
                (match uu____16612 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16616 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16616 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16634 =
                              let uu____16638 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16638
                               in
                            FStar_All.pipe_right uu____16634
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16659 = occurs_check ctx_uv rhs1  in
                          (match uu____16659 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16688 =
                                   let uu____16690 = FStar_Option.get msg  in
                                   Prims.op_Hat "occurs-check failed: "
                                     uu____16690
                                    in
                                 giveup_or_defer env orig wl uu____16688
                               else
                                 (let uu____16696 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____16696
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____16703 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____16703
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____16707 =
                                         let uu____16709 =
                                           names_to_string1 fvs2  in
                                         let uu____16711 =
                                           names_to_string1 fvs1  in
                                         let uu____16713 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____16709 uu____16711
                                           uu____16713
                                          in
                                       giveup_or_defer env orig wl
                                         uu____16707)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16725 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____16732 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16732 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16758 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16758
                             | (FStar_Util.Inl msg,uu____16760) ->
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
                  (let uu____16805 =
                     let uu____16822 = quasi_pattern env lhs  in
                     let uu____16829 = quasi_pattern env rhs  in
                     (uu____16822, uu____16829)  in
                   match uu____16805 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16872 = lhs  in
                       (match uu____16872 with
                        | ({ FStar_Syntax_Syntax.n = uu____16873;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____16875;_},u_lhs,uu____16877)
                            ->
                            let uu____16880 = rhs  in
                            (match uu____16880 with
                             | (uu____16881,u_rhs,uu____16883) ->
                                 let uu____16884 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16884
                                 then
                                   let uu____16891 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16891
                                 else
                                   (let uu____16894 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16894 with
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
                                        let uu____16926 =
                                          let uu____16933 =
                                            let uu____16936 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16936
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16933
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____16926 with
                                         | (uu____16948,w,wl1) ->
                                             let w_app =
                                               let uu____16954 =
                                                 let uu____16959 =
                                                   FStar_List.map
                                                     (fun uu____16970  ->
                                                        match uu____16970
                                                        with
                                                        | (z,uu____16978) ->
                                                            let uu____16983 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____16983) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____16959
                                                  in
                                               uu____16954
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16985 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16985
                                               then
                                                 let uu____16990 =
                                                   let uu____16994 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16996 =
                                                     let uu____17000 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____17002 =
                                                       let uu____17006 =
                                                         term_to_string w  in
                                                       let uu____17008 =
                                                         let uu____17012 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____17021 =
                                                           let uu____17025 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____17034 =
                                                             let uu____17038
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____17038]
                                                              in
                                                           uu____17025 ::
                                                             uu____17034
                                                            in
                                                         uu____17012 ::
                                                           uu____17021
                                                          in
                                                       uu____17006 ::
                                                         uu____17008
                                                        in
                                                     uu____17000 ::
                                                       uu____17002
                                                      in
                                                   uu____16994 :: uu____16996
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16990
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____17055 =
                                                     let uu____17060 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____17060)  in
                                                   TERM uu____17055  in
                                                 let uu____17061 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____17061
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____17069 =
                                                        let uu____17074 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____17074)
                                                         in
                                                      TERM uu____17069  in
                                                    [s1; s2])
                                                  in
                                               let uu____17075 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____17075))))))
                   | uu____17076 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____17147 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____17147
            then
              let uu____17152 = FStar_Syntax_Print.term_to_string t1  in
              let uu____17154 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____17156 = FStar_Syntax_Print.term_to_string t2  in
              let uu____17158 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____17152 uu____17154 uu____17156 uu____17158
            else ());
           (let uu____17169 = FStar_Syntax_Util.head_and_args t1  in
            match uu____17169 with
            | (head1,args1) ->
                let uu____17212 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____17212 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17282 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17282 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              k false (defer "universe constraints" orig wl3))
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17308 =
                         let uu____17310 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____17312 = args_to_string args1  in
                         let uu____17316 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____17318 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____17310 uu____17312 uu____17316 uu____17318
                          in
                       giveup env1 uu____17308 orig
                     else
                       (let uu____17325 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17330 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17330 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17325
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2508_17334 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2508_17334.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2508_17334.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2508_17334.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2508_17334.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2508_17334.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2508_17334.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2508_17334.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2508_17334.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17344 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17344
                                    else solve env1 wl2))
                        else
                          (let uu____17349 = base_and_refinement env1 t1  in
                           match uu____17349 with
                           | (base1,refinement1) ->
                               let uu____17374 = base_and_refinement env1 t2
                                  in
                               (match uu____17374 with
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
                                           let uu____17539 =
                                             FStar_List.fold_right
                                               (fun uu____17579  ->
                                                  fun uu____17580  ->
                                                    match (uu____17579,
                                                            uu____17580)
                                                    with
                                                    | (((a1,uu____17632),
                                                        (a2,uu____17634)),
                                                       (probs,wl3)) ->
                                                        let uu____17683 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17683
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17539 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17726 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17726
                                                 then
                                                   let uu____17731 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17731
                                                 else ());
                                                (let uu____17737 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17737
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
                                                    (let uu____17764 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17764 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17780 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17780
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17788 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17788))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____17812 =
                                                    mk_sub_probs wl3  in
                                                  match uu____17812 with
                                                  | (subprobs,wl4) ->
                                                      let wl5 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          [] wl4
                                                         in
                                                      let uu____17826 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____17826)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17852 =
                                           match uu____17852 with
                                           | (prob,reason) ->
                                               ((let uu____17863 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17863
                                                 then
                                                   let uu____17868 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____17870 =
                                                     prob_to_string env2 prob
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____17868 uu____17870
                                                     reason
                                                 else ());
                                                (let uu____17875 =
                                                   let uu____17884 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____17887 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____17884, uu____17887)
                                                    in
                                                 match uu____17875 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____17900 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____17900 with
                                                      | (head1',uu____17918)
                                                          ->
                                                          let uu____17943 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____17943
                                                           with
                                                           | (head2',uu____17961)
                                                               ->
                                                               let uu____17986
                                                                 =
                                                                 let uu____17991
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____17992
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____17991,
                                                                   uu____17992)
                                                                  in
                                                               (match uu____17986
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____17994
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17994
                                                                    then
                                                                    let uu____17999
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____18001
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____18003
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____18005
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17999
                                                                    uu____18001
                                                                    uu____18003
                                                                    uu____18005
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____18010
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2594_18018
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2594_18018.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2594_18018.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2594_18018.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2594_18018.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2594_18018.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2594_18018.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2594_18018.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2594_18018.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____18020
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____18020
                                                                    then
                                                                    let uu____18025
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____18025
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____18030 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____18042 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____18042 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____18050 =
                                             let uu____18051 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____18051.FStar_Syntax_Syntax.n
                                              in
                                           match uu____18050 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____18056 -> false  in
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
                                          | uu____18059 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____18062 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2614_18098 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2614_18098.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2614_18098.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2614_18098.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2614_18098.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2614_18098.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2614_18098.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2614_18098.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2614_18098.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____18174 = destruct_flex_t scrutinee wl1  in
             match uu____18174 with
             | ((_t,uv,_args),wl2) ->
                 let uu____18185 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____18185 with
                  | (xs,pat_term,uu____18201,uu____18202) ->
                      let uu____18207 =
                        FStar_List.fold_left
                          (fun uu____18230  ->
                             fun x  ->
                               match uu____18230 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18251 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18251 with
                                    | (uu____18270,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____18207 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____18291 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18291 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2654_18308 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2654_18308.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2654_18308.umax_heuristic_ok);
                                    tcenv = (uu___2654_18308.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18320 = solve env1 wl'  in
                                (match uu____18320 with
                                 | Success (uu____18323,imps) ->
                                     let wl'1 =
                                       let uu___2662_18326 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2662_18326.wl_deferred);
                                         ctr = (uu___2662_18326.ctr);
                                         defer_ok =
                                           (uu___2662_18326.defer_ok);
                                         smt_ok = (uu___2662_18326.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2662_18326.umax_heuristic_ok);
                                         tcenv = (uu___2662_18326.tcenv);
                                         wl_implicits =
                                           (uu___2662_18326.wl_implicits)
                                       }  in
                                     let uu____18327 = solve env1 wl'1  in
                                     (match uu____18327 with
                                      | Success (uu____18330,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2670_18334 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2670_18334.attempting);
                                                 wl_deferred =
                                                   (uu___2670_18334.wl_deferred);
                                                 ctr = (uu___2670_18334.ctr);
                                                 defer_ok =
                                                   (uu___2670_18334.defer_ok);
                                                 smt_ok =
                                                   (uu___2670_18334.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2670_18334.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2670_18334.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____18335 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18342 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18365 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18365
                 then
                   let uu____18370 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18372 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18370 uu____18372
                 else ());
                (let uu____18377 =
                   let uu____18398 =
                     let uu____18407 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18407)  in
                   let uu____18414 =
                     let uu____18423 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18423)  in
                   (uu____18398, uu____18414)  in
                 match uu____18377 with
                 | ((uu____18453,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18456;
                                   FStar_Syntax_Syntax.vars = uu____18457;_}),
                    (s,t)) ->
                     let uu____18528 =
                       let uu____18530 = is_flex scrutinee  in
                       Prims.op_Negation uu____18530  in
                     if uu____18528
                     then
                       ((let uu____18541 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18541
                         then
                           let uu____18546 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18546
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18565 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18565
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18580 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18580
                           then
                             let uu____18585 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18587 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18585 uu____18587
                           else ());
                          (let pat_discriminates uu___28_18612 =
                             match uu___28_18612 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18628;
                                  FStar_Syntax_Syntax.p = uu____18629;_},FStar_Pervasives_Native.None
                                ,uu____18630) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18644;
                                  FStar_Syntax_Syntax.p = uu____18645;_},FStar_Pervasives_Native.None
                                ,uu____18646) -> true
                             | uu____18673 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18776 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18776 with
                                       | (uu____18778,uu____18779,t') ->
                                           let uu____18797 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18797 with
                                            | (FullMatch ,uu____18809) ->
                                                true
                                            | (HeadMatch
                                               uu____18823,uu____18824) ->
                                                true
                                            | uu____18839 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18876 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18876
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18887 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18887 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18975,uu____18976) ->
                                       branches1
                                   | uu____19121 -> branches  in
                                 let uu____19176 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19185 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19185 with
                                        | (p,uu____19189,uu____19190) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19219  -> FStar_Util.Inr _19219)
                                   uu____19176))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19249 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19249 with
                                | (p,uu____19258,e) ->
                                    ((let uu____19277 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19277
                                      then
                                        let uu____19282 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19284 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19282 uu____19284
                                      else ());
                                     (let uu____19289 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19304  -> FStar_Util.Inr _19304)
                                        uu____19289)))))
                 | ((s,t),(uu____19307,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19310;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19311;_}))
                     ->
                     let uu____19380 =
                       let uu____19382 = is_flex scrutinee  in
                       Prims.op_Negation uu____19382  in
                     if uu____19380
                     then
                       ((let uu____19393 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19393
                         then
                           let uu____19398 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19398
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19417 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19417
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19432 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19432
                           then
                             let uu____19437 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19439 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19437 uu____19439
                           else ());
                          (let pat_discriminates uu___28_19464 =
                             match uu___28_19464 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19480;
                                  FStar_Syntax_Syntax.p = uu____19481;_},FStar_Pervasives_Native.None
                                ,uu____19482) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19496;
                                  FStar_Syntax_Syntax.p = uu____19497;_},FStar_Pervasives_Native.None
                                ,uu____19498) -> true
                             | uu____19525 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19628 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19628 with
                                       | (uu____19630,uu____19631,t') ->
                                           let uu____19649 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19649 with
                                            | (FullMatch ,uu____19661) ->
                                                true
                                            | (HeadMatch
                                               uu____19675,uu____19676) ->
                                                true
                                            | uu____19691 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19728 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19728
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19739 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19739 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19827,uu____19828) ->
                                       branches1
                                   | uu____19973 -> branches  in
                                 let uu____20028 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____20037 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____20037 with
                                        | (p,uu____20041,uu____20042) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _20071  -> FStar_Util.Inr _20071)
                                   uu____20028))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____20101 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____20101 with
                                | (p,uu____20110,e) ->
                                    ((let uu____20129 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____20129
                                      then
                                        let uu____20134 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____20136 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____20134 uu____20136
                                      else ());
                                     (let uu____20141 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _20156  -> FStar_Util.Inr _20156)
                                        uu____20141)))))
                 | uu____20157 ->
                     ((let uu____20179 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____20179
                       then
                         let uu____20184 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____20186 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20184 uu____20186
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20232 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20232
            then
              let uu____20237 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20239 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20241 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20243 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20237 uu____20239 uu____20241 uu____20243
            else ());
           (let uu____20248 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20248 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20279,uu____20280) ->
                     let rec may_relate head3 =
                       let uu____20308 =
                         let uu____20309 = FStar_Syntax_Subst.compress head3
                            in
                         uu____20309.FStar_Syntax_Syntax.n  in
                       match uu____20308 with
                       | FStar_Syntax_Syntax.Tm_name uu____20313 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20315 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20340 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20340 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20342 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20345
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20346 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20349,uu____20350) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20392) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20398) ->
                           may_relate t
                       | uu____20403 -> false  in
                     let uu____20405 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20405 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20426 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20426
                          then
                            let uu____20429 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20429 with
                             | (guard,wl2) ->
                                 let uu____20436 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20436)
                          else
                            (let uu____20439 =
                               let uu____20441 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____20443 =
                                 let uu____20445 =
                                   let uu____20449 =
                                     delta_depth_of_term env1 head1  in
                                   FStar_Util.bind_opt uu____20449
                                     (fun x  ->
                                        let uu____20456 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____20456)
                                    in
                                 FStar_Util.dflt "" uu____20445  in
                               let uu____20461 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               let uu____20463 =
                                 let uu____20465 =
                                   let uu____20469 =
                                     delta_depth_of_term env1 head2  in
                                   FStar_Util.bind_opt uu____20469
                                     (fun x  ->
                                        let uu____20476 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____20476)
                                    in
                                 FStar_Util.dflt "" uu____20465  in
                               FStar_Util.format4
                                 "head mismatch (%s (%s) vs %s (%s))"
                                 uu____20441 uu____20443 uu____20461
                                 uu____20463
                                in
                             giveup env1 uu____20439 orig))
                 | (HeadMatch (true ),uu____20482) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20497 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20497 with
                        | (guard,wl2) ->
                            let uu____20504 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20504)
                     else
                       (let uu____20507 =
                          let uu____20509 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____20511 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____20509 uu____20511
                           in
                        giveup env1 uu____20507 orig)
                 | (uu____20514,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2843_20528 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2843_20528.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2843_20528.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2843_20528.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2843_20528.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2843_20528.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2843_20528.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2843_20528.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2843_20528.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20555 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20555
          then
            let uu____20558 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20558
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20564 =
                let uu____20567 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20567  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20564 t1);
             (let uu____20586 =
                let uu____20589 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20589  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20586 t2);
             (let uu____20608 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20608
              then
                let uu____20612 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20614 =
                  let uu____20616 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20618 =
                    let uu____20620 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____20620  in
                  Prims.op_Hat uu____20616 uu____20618  in
                let uu____20623 =
                  let uu____20625 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20627 =
                    let uu____20629 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____20629  in
                  Prims.op_Hat uu____20625 uu____20627  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20612 uu____20614 uu____20623
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20636,uu____20637) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20661,FStar_Syntax_Syntax.Tm_delayed uu____20662) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20686,uu____20687) ->
                  let uu____20714 =
                    let uu___2874_20715 = problem  in
                    let uu____20716 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2874_20715.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20716;
                      FStar_TypeChecker_Common.relation =
                        (uu___2874_20715.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2874_20715.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2874_20715.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2874_20715.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2874_20715.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2874_20715.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2874_20715.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2874_20715.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20714 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20717,uu____20718) ->
                  let uu____20725 =
                    let uu___2880_20726 = problem  in
                    let uu____20727 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2880_20726.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20727;
                      FStar_TypeChecker_Common.relation =
                        (uu___2880_20726.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2880_20726.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2880_20726.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2880_20726.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2880_20726.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2880_20726.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2880_20726.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2880_20726.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20725 wl
              | (uu____20728,FStar_Syntax_Syntax.Tm_ascribed uu____20729) ->
                  let uu____20756 =
                    let uu___2886_20757 = problem  in
                    let uu____20758 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2886_20757.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2886_20757.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2886_20757.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20758;
                      FStar_TypeChecker_Common.element =
                        (uu___2886_20757.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2886_20757.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2886_20757.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2886_20757.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2886_20757.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2886_20757.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20756 wl
              | (uu____20759,FStar_Syntax_Syntax.Tm_meta uu____20760) ->
                  let uu____20767 =
                    let uu___2892_20768 = problem  in
                    let uu____20769 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2892_20768.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2892_20768.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2892_20768.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20769;
                      FStar_TypeChecker_Common.element =
                        (uu___2892_20768.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2892_20768.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2892_20768.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2892_20768.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2892_20768.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2892_20768.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20767 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____20771),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____20773)) ->
                  let uu____20782 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____20782
              | (FStar_Syntax_Syntax.Tm_bvar uu____20783,uu____20784) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____20786,FStar_Syntax_Syntax.Tm_bvar uu____20787) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___29_20857 =
                    match uu___29_20857 with
                    | [] -> c
                    | bs ->
                        let uu____20885 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____20885
                     in
                  let uu____20896 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____20896 with
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
                                    let uu____21045 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____21045
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
                  let mk_t t l uu___30_21134 =
                    match uu___30_21134 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____21176 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____21176 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____21321 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____21322 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21321
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21322 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21324,uu____21325) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21356 -> true
                    | uu____21376 -> false  in
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
                      (let uu____21436 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___2994_21444 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___2994_21444.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___2994_21444.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___2994_21444.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___2994_21444.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___2994_21444.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___2994_21444.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___2994_21444.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___2994_21444.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___2994_21444.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___2994_21444.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___2994_21444.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___2994_21444.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___2994_21444.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___2994_21444.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___2994_21444.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___2994_21444.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___2994_21444.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___2994_21444.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___2994_21444.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___2994_21444.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___2994_21444.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___2994_21444.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___2994_21444.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___2994_21444.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___2994_21444.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___2994_21444.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___2994_21444.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___2994_21444.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___2994_21444.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___2994_21444.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___2994_21444.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___2994_21444.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___2994_21444.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___2994_21444.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___2994_21444.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___2994_21444.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___2994_21444.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___2994_21444.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___2994_21444.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___2994_21444.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___2994_21444.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___2994_21444.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21436 with
                       | (uu____21449,ty,uu____21451) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21460 =
                                 let uu____21461 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21461.FStar_Syntax_Syntax.n  in
                               match uu____21460 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21464 ->
                                   let uu____21471 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21471
                               | uu____21472 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21475 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21475
                             then
                               let uu____21480 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21482 =
                                 let uu____21484 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21484
                                  in
                               let uu____21485 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21480 uu____21482 uu____21485
                             else ());
                            r1))
                     in
                  let uu____21490 =
                    let uu____21507 = maybe_eta t1  in
                    let uu____21514 = maybe_eta t2  in
                    (uu____21507, uu____21514)  in
                  (match uu____21490 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3015_21556 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3015_21556.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3015_21556.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3015_21556.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3015_21556.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3015_21556.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3015_21556.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3015_21556.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3015_21556.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21577 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21577
                       then
                         let uu____21580 = destruct_flex_t not_abs wl  in
                         (match uu____21580 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3032_21597 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3032_21597.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3032_21597.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3032_21597.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3032_21597.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3032_21597.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3032_21597.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3032_21597.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3032_21597.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21621 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21621
                       then
                         let uu____21624 = destruct_flex_t not_abs wl  in
                         (match uu____21624 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3032_21641 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3032_21641.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3032_21641.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3032_21641.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3032_21641.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3032_21641.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3032_21641.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3032_21641.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3032_21641.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____21645 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21663,FStar_Syntax_Syntax.Tm_abs uu____21664) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21695 -> true
                    | uu____21715 -> false  in
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
                      (let uu____21775 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___2994_21783 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___2994_21783.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___2994_21783.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___2994_21783.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___2994_21783.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___2994_21783.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___2994_21783.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___2994_21783.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___2994_21783.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___2994_21783.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___2994_21783.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___2994_21783.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___2994_21783.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___2994_21783.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___2994_21783.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___2994_21783.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___2994_21783.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___2994_21783.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___2994_21783.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___2994_21783.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___2994_21783.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___2994_21783.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___2994_21783.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___2994_21783.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___2994_21783.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___2994_21783.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___2994_21783.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___2994_21783.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___2994_21783.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___2994_21783.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___2994_21783.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___2994_21783.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___2994_21783.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___2994_21783.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___2994_21783.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___2994_21783.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___2994_21783.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___2994_21783.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___2994_21783.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___2994_21783.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___2994_21783.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___2994_21783.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___2994_21783.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21775 with
                       | (uu____21788,ty,uu____21790) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21799 =
                                 let uu____21800 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21800.FStar_Syntax_Syntax.n  in
                               match uu____21799 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21803 ->
                                   let uu____21810 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21810
                               | uu____21811 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21814 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21814
                             then
                               let uu____21819 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21821 =
                                 let uu____21823 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21823
                                  in
                               let uu____21824 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21819 uu____21821 uu____21824
                             else ());
                            r1))
                     in
                  let uu____21829 =
                    let uu____21846 = maybe_eta t1  in
                    let uu____21853 = maybe_eta t2  in
                    (uu____21846, uu____21853)  in
                  (match uu____21829 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3015_21895 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3015_21895.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3015_21895.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3015_21895.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3015_21895.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3015_21895.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3015_21895.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3015_21895.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3015_21895.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21916 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21916
                       then
                         let uu____21919 = destruct_flex_t not_abs wl  in
                         (match uu____21919 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3032_21936 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3032_21936.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3032_21936.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3032_21936.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3032_21936.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3032_21936.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3032_21936.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3032_21936.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3032_21936.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21960 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21960
                       then
                         let uu____21963 = destruct_flex_t not_abs wl  in
                         (match uu____21963 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3032_21980 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3032_21980.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3032_21980.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3032_21980.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3032_21980.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3032_21980.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3032_21980.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3032_21980.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3032_21980.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____21984 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____22014 =
                    let uu____22019 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____22019 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3055_22047 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3055_22047.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3055_22047.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3057_22049 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3057_22049.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3057_22049.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____22050,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3055_22065 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3055_22065.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3055_22065.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3057_22067 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3057_22067.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3057_22067.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____22068 -> (x1, x2)  in
                  (match uu____22014 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____22087 = as_refinement false env t11  in
                       (match uu____22087 with
                        | (x12,phi11) ->
                            let uu____22095 = as_refinement false env t21  in
                            (match uu____22095 with
                             | (x22,phi21) ->
                                 ((let uu____22104 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____22104
                                   then
                                     ((let uu____22109 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____22111 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22113 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____22109
                                         uu____22111 uu____22113);
                                      (let uu____22116 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____22118 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22120 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____22116
                                         uu____22118 uu____22120))
                                   else ());
                                  (let uu____22125 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____22125 with
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
                                         let uu____22196 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____22196
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22208 =
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
                                         (let uu____22221 =
                                            let uu____22224 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22224
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22221
                                            (p_guard base_prob));
                                         (let uu____22243 =
                                            let uu____22246 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22246
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22243
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22265 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22265)
                                          in
                                       let has_uvars =
                                         (let uu____22270 =
                                            let uu____22272 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22272
                                             in
                                          Prims.op_Negation uu____22270) ||
                                           (let uu____22276 =
                                              let uu____22278 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22278
                                               in
                                            Prims.op_Negation uu____22276)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22282 =
                                           let uu____22287 =
                                             let uu____22296 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22296]  in
                                           mk_t_problem wl1 uu____22287 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22282 with
                                          | (ref_prob,wl2) ->
                                              let uu____22318 =
                                                solve env1
                                                  (let uu___3099_22320 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3099_22320.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3099_22320.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3099_22320.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3099_22320.tcenv);
                                                     wl_implicits =
                                                       (uu___3099_22320.wl_implicits)
                                                   })
                                                 in
                                              (match uu____22318 with
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
                                               | Success uu____22337 ->
                                                   let guard =
                                                     let uu____22345 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____22345
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___3110_22354 =
                                                       wl3  in
                                                     {
                                                       attempting =
                                                         (uu___3110_22354.attempting);
                                                       wl_deferred =
                                                         (uu___3110_22354.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            Prims.int_one);
                                                       defer_ok =
                                                         (uu___3110_22354.defer_ok);
                                                       smt_ok =
                                                         (uu___3110_22354.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___3110_22354.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___3110_22354.tcenv);
                                                       wl_implicits =
                                                         (uu___3110_22354.wl_implicits)
                                                     }  in
                                                   let uu____22356 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____22356))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22359,FStar_Syntax_Syntax.Tm_uvar uu____22360) ->
                  let uu____22385 = destruct_flex_t t1 wl  in
                  (match uu____22385 with
                   | (f1,wl1) ->
                       let uu____22392 = destruct_flex_t t2 wl1  in
                       (match uu____22392 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22399;
                    FStar_Syntax_Syntax.pos = uu____22400;
                    FStar_Syntax_Syntax.vars = uu____22401;_},uu____22402),FStar_Syntax_Syntax.Tm_uvar
                 uu____22403) ->
                  let uu____22452 = destruct_flex_t t1 wl  in
                  (match uu____22452 with
                   | (f1,wl1) ->
                       let uu____22459 = destruct_flex_t t2 wl1  in
                       (match uu____22459 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22466,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22467;
                    FStar_Syntax_Syntax.pos = uu____22468;
                    FStar_Syntax_Syntax.vars = uu____22469;_},uu____22470))
                  ->
                  let uu____22519 = destruct_flex_t t1 wl  in
                  (match uu____22519 with
                   | (f1,wl1) ->
                       let uu____22526 = destruct_flex_t t2 wl1  in
                       (match uu____22526 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22533;
                    FStar_Syntax_Syntax.pos = uu____22534;
                    FStar_Syntax_Syntax.vars = uu____22535;_},uu____22536),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22537;
                    FStar_Syntax_Syntax.pos = uu____22538;
                    FStar_Syntax_Syntax.vars = uu____22539;_},uu____22540))
                  ->
                  let uu____22613 = destruct_flex_t t1 wl  in
                  (match uu____22613 with
                   | (f1,wl1) ->
                       let uu____22620 = destruct_flex_t t2 wl1  in
                       (match uu____22620 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22627,uu____22628) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22641 = destruct_flex_t t1 wl  in
                  (match uu____22641 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22648;
                    FStar_Syntax_Syntax.pos = uu____22649;
                    FStar_Syntax_Syntax.vars = uu____22650;_},uu____22651),uu____22652)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22689 = destruct_flex_t t1 wl  in
                  (match uu____22689 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22696,FStar_Syntax_Syntax.Tm_uvar uu____22697) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22710,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22711;
                    FStar_Syntax_Syntax.pos = uu____22712;
                    FStar_Syntax_Syntax.vars = uu____22713;_},uu____22714))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22751,FStar_Syntax_Syntax.Tm_arrow uu____22752) ->
                  solve_t' env
                    (let uu___3210_22780 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3210_22780.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3210_22780.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3210_22780.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3210_22780.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3210_22780.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3210_22780.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3210_22780.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3210_22780.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3210_22780.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22781;
                    FStar_Syntax_Syntax.pos = uu____22782;
                    FStar_Syntax_Syntax.vars = uu____22783;_},uu____22784),FStar_Syntax_Syntax.Tm_arrow
                 uu____22785) ->
                  solve_t' env
                    (let uu___3210_22837 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3210_22837.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3210_22837.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3210_22837.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3210_22837.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3210_22837.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3210_22837.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3210_22837.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3210_22837.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3210_22837.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22838,FStar_Syntax_Syntax.Tm_uvar uu____22839) ->
                  let uu____22852 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22852
              | (uu____22853,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22854;
                    FStar_Syntax_Syntax.pos = uu____22855;
                    FStar_Syntax_Syntax.vars = uu____22856;_},uu____22857))
                  ->
                  let uu____22894 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22894
              | (FStar_Syntax_Syntax.Tm_uvar uu____22895,uu____22896) ->
                  let uu____22909 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22909
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22910;
                    FStar_Syntax_Syntax.pos = uu____22911;
                    FStar_Syntax_Syntax.vars = uu____22912;_},uu____22913),uu____22914)
                  ->
                  let uu____22951 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22951
              | (FStar_Syntax_Syntax.Tm_refine uu____22952,uu____22953) ->
                  let t21 =
                    let uu____22961 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____22961  in
                  solve_t env
                    (let uu___3245_22987 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3245_22987.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3245_22987.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3245_22987.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3245_22987.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3245_22987.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3245_22987.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3245_22987.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3245_22987.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3245_22987.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22988,FStar_Syntax_Syntax.Tm_refine uu____22989) ->
                  let t11 =
                    let uu____22997 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22997  in
                  solve_t env
                    (let uu___3252_23023 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3252_23023.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3252_23023.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3252_23023.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3252_23023.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3252_23023.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3252_23023.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3252_23023.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3252_23023.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3252_23023.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____23105 =
                    let uu____23106 = guard_of_prob env wl problem t1 t2  in
                    match uu____23106 with
                    | (guard,wl1) ->
                        let uu____23113 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____23113
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23332 = br1  in
                        (match uu____23332 with
                         | (p1,w1,uu____23361) ->
                             let uu____23378 = br2  in
                             (match uu____23378 with
                              | (p2,w2,uu____23401) ->
                                  let uu____23406 =
                                    let uu____23408 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23408  in
                                  if uu____23406
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23435 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23435 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23472 = br2  in
                                         (match uu____23472 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23505 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23505
                                                 in
                                              let uu____23510 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23541,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23562) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23621 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23621 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23510
                                                (fun uu____23693  ->
                                                   match uu____23693 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23730 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23730
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____23751
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____23751
                                                              then
                                                                let uu____23756
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____23758
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____23756
                                                                  uu____23758
                                                              else ());
                                                             (let uu____23764
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____23764
                                                                (fun
                                                                   uu____23800
                                                                    ->
                                                                   match uu____23800
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
                    | uu____23929 -> FStar_Pervasives_Native.None  in
                  let uu____23970 = solve_branches wl brs1 brs2  in
                  (match uu____23970 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____24021 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____24021 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____24055 =
                                FStar_List.map
                                  (fun uu____24067  ->
                                     match uu____24067 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____24055  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____24076 =
                              let uu____24077 =
                                let uu____24078 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____24078
                                  (let uu___3351_24086 = wl3  in
                                   {
                                     attempting =
                                       (uu___3351_24086.attempting);
                                     wl_deferred =
                                       (uu___3351_24086.wl_deferred);
                                     ctr = (uu___3351_24086.ctr);
                                     defer_ok = (uu___3351_24086.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3351_24086.umax_heuristic_ok);
                                     tcenv = (uu___3351_24086.tcenv);
                                     wl_implicits =
                                       (uu___3351_24086.wl_implicits)
                                   })
                                 in
                              solve env uu____24077  in
                            (match uu____24076 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____24091 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____24098,uu____24099) ->
                  let head1 =
                    let uu____24123 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24123
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24169 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24169
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24215 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24215
                    then
                      let uu____24219 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24221 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24223 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24219 uu____24221 uu____24223
                    else ());
                   (let no_free_uvars t =
                      (let uu____24237 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24237) &&
                        (let uu____24241 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24241)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24258 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24258 = FStar_Syntax_Util.Equal  in
                    let uu____24259 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24259
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24263 = equal t1 t2  in
                         (if uu____24263
                          then
                            let uu____24266 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24266
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24271 =
                            let uu____24278 = equal t1 t2  in
                            if uu____24278
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24291 = mk_eq2 wl env orig t1 t2  in
                               match uu____24291 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24271 with
                          | (guard,wl1) ->
                              let uu____24312 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24312))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24315,uu____24316) ->
                  let head1 =
                    let uu____24324 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24324
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24370 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24370
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24416 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24416
                    then
                      let uu____24420 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24422 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24424 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24420 uu____24422 uu____24424
                    else ());
                   (let no_free_uvars t =
                      (let uu____24438 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24438) &&
                        (let uu____24442 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24442)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24459 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24459 = FStar_Syntax_Util.Equal  in
                    let uu____24460 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24460
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24464 = equal t1 t2  in
                         (if uu____24464
                          then
                            let uu____24467 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24467
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24472 =
                            let uu____24479 = equal t1 t2  in
                            if uu____24479
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24492 = mk_eq2 wl env orig t1 t2  in
                               match uu____24492 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24472 with
                          | (guard,wl1) ->
                              let uu____24513 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24513))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24516,uu____24517) ->
                  let head1 =
                    let uu____24519 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24519
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24565 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24565
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24611 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24611
                    then
                      let uu____24615 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24617 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24619 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24615 uu____24617 uu____24619
                    else ());
                   (let no_free_uvars t =
                      (let uu____24633 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24633) &&
                        (let uu____24637 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24637)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24654 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24654 = FStar_Syntax_Util.Equal  in
                    let uu____24655 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24655
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24659 = equal t1 t2  in
                         (if uu____24659
                          then
                            let uu____24662 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24662
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24667 =
                            let uu____24674 = equal t1 t2  in
                            if uu____24674
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24687 = mk_eq2 wl env orig t1 t2  in
                               match uu____24687 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24667 with
                          | (guard,wl1) ->
                              let uu____24708 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24708))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24711,uu____24712) ->
                  let head1 =
                    let uu____24714 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24714
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24760 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24760
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24806 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24806
                    then
                      let uu____24810 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24812 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24814 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24810 uu____24812 uu____24814
                    else ());
                   (let no_free_uvars t =
                      (let uu____24828 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24828) &&
                        (let uu____24832 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24832)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24849 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24849 = FStar_Syntax_Util.Equal  in
                    let uu____24850 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24850
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24854 = equal t1 t2  in
                         (if uu____24854
                          then
                            let uu____24857 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24857
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24862 =
                            let uu____24869 = equal t1 t2  in
                            if uu____24869
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24882 = mk_eq2 wl env orig t1 t2  in
                               match uu____24882 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24862 with
                          | (guard,wl1) ->
                              let uu____24903 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24903))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____24906,uu____24907) ->
                  let head1 =
                    let uu____24909 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24909
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24955 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24955
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25001 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25001
                    then
                      let uu____25005 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25007 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25009 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25005 uu____25007 uu____25009
                    else ());
                   (let no_free_uvars t =
                      (let uu____25023 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25023) &&
                        (let uu____25027 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25027)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25044 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25044 = FStar_Syntax_Util.Equal  in
                    let uu____25045 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25045
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25049 = equal t1 t2  in
                         (if uu____25049
                          then
                            let uu____25052 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25052
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25057 =
                            let uu____25064 = equal t1 t2  in
                            if uu____25064
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25077 = mk_eq2 wl env orig t1 t2  in
                               match uu____25077 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25057 with
                          | (guard,wl1) ->
                              let uu____25098 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25098))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____25101,uu____25102) ->
                  let head1 =
                    let uu____25120 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25120
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25166 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25166
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25212 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25212
                    then
                      let uu____25216 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25218 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25220 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25216 uu____25218 uu____25220
                    else ());
                   (let no_free_uvars t =
                      (let uu____25234 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25234) &&
                        (let uu____25238 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25238)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25255 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25255 = FStar_Syntax_Util.Equal  in
                    let uu____25256 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25256
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25260 = equal t1 t2  in
                         (if uu____25260
                          then
                            let uu____25263 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25263
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25268 =
                            let uu____25275 = equal t1 t2  in
                            if uu____25275
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25288 = mk_eq2 wl env orig t1 t2  in
                               match uu____25288 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25268 with
                          | (guard,wl1) ->
                              let uu____25309 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25309))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25312,FStar_Syntax_Syntax.Tm_match uu____25313) ->
                  let head1 =
                    let uu____25337 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25337
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25383 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25383
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25429 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25429
                    then
                      let uu____25433 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25435 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25437 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25433 uu____25435 uu____25437
                    else ());
                   (let no_free_uvars t =
                      (let uu____25451 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25451) &&
                        (let uu____25455 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25455)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25472 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25472 = FStar_Syntax_Util.Equal  in
                    let uu____25473 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25473
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25477 = equal t1 t2  in
                         (if uu____25477
                          then
                            let uu____25480 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25480
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25485 =
                            let uu____25492 = equal t1 t2  in
                            if uu____25492
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25505 = mk_eq2 wl env orig t1 t2  in
                               match uu____25505 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25485 with
                          | (guard,wl1) ->
                              let uu____25526 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25526))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25529,FStar_Syntax_Syntax.Tm_uinst uu____25530) ->
                  let head1 =
                    let uu____25538 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25538
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25578 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25578
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25618 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25618
                    then
                      let uu____25622 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25624 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25626 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25622 uu____25624 uu____25626
                    else ());
                   (let no_free_uvars t =
                      (let uu____25640 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25640) &&
                        (let uu____25644 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25644)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25661 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25661 = FStar_Syntax_Util.Equal  in
                    let uu____25662 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25662
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25666 = equal t1 t2  in
                         (if uu____25666
                          then
                            let uu____25669 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25669
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25674 =
                            let uu____25681 = equal t1 t2  in
                            if uu____25681
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25694 = mk_eq2 wl env orig t1 t2  in
                               match uu____25694 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25674 with
                          | (guard,wl1) ->
                              let uu____25715 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25715))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25718,FStar_Syntax_Syntax.Tm_name uu____25719) ->
                  let head1 =
                    let uu____25721 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25721
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25761 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25761
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25801 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25801
                    then
                      let uu____25805 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25807 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25809 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25805 uu____25807 uu____25809
                    else ());
                   (let no_free_uvars t =
                      (let uu____25823 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25823) &&
                        (let uu____25827 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25827)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25844 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25844 = FStar_Syntax_Util.Equal  in
                    let uu____25845 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25845
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25849 = equal t1 t2  in
                         (if uu____25849
                          then
                            let uu____25852 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25852
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25857 =
                            let uu____25864 = equal t1 t2  in
                            if uu____25864
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25877 = mk_eq2 wl env orig t1 t2  in
                               match uu____25877 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25857 with
                          | (guard,wl1) ->
                              let uu____25898 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25898))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25901,FStar_Syntax_Syntax.Tm_constant uu____25902) ->
                  let head1 =
                    let uu____25904 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25904
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25944 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25944
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25984 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25984
                    then
                      let uu____25988 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25990 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25992 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25988 uu____25990 uu____25992
                    else ());
                   (let no_free_uvars t =
                      (let uu____26006 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26006) &&
                        (let uu____26010 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26010)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____26027 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26027 = FStar_Syntax_Util.Equal  in
                    let uu____26028 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26028
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26032 = equal t1 t2  in
                         (if uu____26032
                          then
                            let uu____26035 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26035
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26040 =
                            let uu____26047 = equal t1 t2  in
                            if uu____26047
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26060 = mk_eq2 wl env orig t1 t2  in
                               match uu____26060 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26040 with
                          | (guard,wl1) ->
                              let uu____26081 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26081))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26084,FStar_Syntax_Syntax.Tm_fvar uu____26085) ->
                  let head1 =
                    let uu____26087 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26087
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26127 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26127
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26167 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26167
                    then
                      let uu____26171 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26173 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26175 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26171 uu____26173 uu____26175
                    else ());
                   (let no_free_uvars t =
                      (let uu____26189 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26189) &&
                        (let uu____26193 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26193)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____26210 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26210 = FStar_Syntax_Util.Equal  in
                    let uu____26211 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26211
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26215 = equal t1 t2  in
                         (if uu____26215
                          then
                            let uu____26218 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26218
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26223 =
                            let uu____26230 = equal t1 t2  in
                            if uu____26230
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26243 = mk_eq2 wl env orig t1 t2  in
                               match uu____26243 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26223 with
                          | (guard,wl1) ->
                              let uu____26264 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26264))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26267,FStar_Syntax_Syntax.Tm_app uu____26268) ->
                  let head1 =
                    let uu____26286 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26286
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26326 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26326
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26366 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26366
                    then
                      let uu____26370 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26372 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26374 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26370 uu____26372 uu____26374
                    else ());
                   (let no_free_uvars t =
                      (let uu____26388 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26388) &&
                        (let uu____26392 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26392)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____26409 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26409 = FStar_Syntax_Util.Equal  in
                    let uu____26410 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26410
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26414 = equal t1 t2  in
                         (if uu____26414
                          then
                            let uu____26417 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26417
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26422 =
                            let uu____26429 = equal t1 t2  in
                            if uu____26429
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26442 = mk_eq2 wl env orig t1 t2  in
                               match uu____26442 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26422 with
                          | (guard,wl1) ->
                              let uu____26463 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26463))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26466,FStar_Syntax_Syntax.Tm_let uu____26467) ->
                  let uu____26494 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26494
                  then
                    let uu____26497 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26497
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____26501,uu____26502) ->
                  let uu____26516 =
                    let uu____26522 =
                      let uu____26524 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26526 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26528 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26530 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26524 uu____26526 uu____26528 uu____26530
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26522)
                     in
                  FStar_Errors.raise_error uu____26516
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26534,FStar_Syntax_Syntax.Tm_let uu____26535) ->
                  let uu____26549 =
                    let uu____26555 =
                      let uu____26557 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26559 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26561 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26563 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26557 uu____26559 uu____26561 uu____26563
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26555)
                     in
                  FStar_Errors.raise_error uu____26549
                    t1.FStar_Syntax_Syntax.pos
              | uu____26567 -> giveup env "head tag mismatch" orig))))

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
        let solve_eq c1_comp c2_comp =
          (let uu____26631 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26631
           then
             let uu____26636 =
               let uu____26638 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26638  in
             let uu____26639 =
               let uu____26641 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26641  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26636 uu____26639
           else ());
          (let uu____26645 =
             let uu____26647 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26647  in
           if uu____26645
           then
             let uu____26650 =
               let uu____26652 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____26654 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____26652 uu____26654
                in
             giveup env uu____26650 orig
           else
             (let uu____26659 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____26659 with
              | (ret_sub_prob,wl1) ->
                  let uu____26667 =
                    FStar_List.fold_right2
                      (fun uu____26704  ->
                         fun uu____26705  ->
                           fun uu____26706  ->
                             match (uu____26704, uu____26705, uu____26706)
                             with
                             | ((a1,uu____26750),(a2,uu____26752),(arg_sub_probs,wl2))
                                 ->
                                 let uu____26785 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____26785 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____26667 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____26815 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____26815  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____26823 = attempt sub_probs wl3  in
                       solve env uu____26823)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____26846 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____26849)::[] -> wp1
              | uu____26874 ->
                  let uu____26885 =
                    let uu____26887 =
                      let uu____26889 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____26889  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____26887
                     in
                  failwith uu____26885
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____26896 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____26896]
              | x -> x  in
            let uu____26898 =
              let uu____26909 =
                let uu____26918 =
                  let uu____26919 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____26919 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____26918  in
              [uu____26909]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____26898;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____26937 = lift_c1 ()  in solve_eq uu____26937 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___31_26946  ->
                       match uu___31_26946 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____26951 -> false))
                in
             let uu____26953 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____26983)::uu____26984,(wp2,uu____26986)::uu____26987)
                   -> (wp1, wp2)
               | uu____27060 ->
                   let uu____27085 =
                     let uu____27091 =
                       let uu____27093 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____27095 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____27093 uu____27095
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____27091)
                      in
                   FStar_Errors.raise_error uu____27085
                     env.FStar_TypeChecker_Env.range
                in
             match uu____26953 with
             | (wpc1,wpc2) ->
                 let uu____27105 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____27105
                 then
                   let uu____27110 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____27110 wl
                 else
                   (let uu____27114 =
                      let uu____27121 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____27121  in
                    match uu____27114 with
                    | (c2_decl,qualifiers) ->
                        let uu____27142 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____27142
                        then
                          let c1_repr =
                            let uu____27149 =
                              let uu____27150 =
                                let uu____27151 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____27151  in
                              let uu____27152 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____27150 uu____27152
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____27149
                             in
                          let c2_repr =
                            let uu____27154 =
                              let uu____27155 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____27156 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____27155 uu____27156
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____27154
                             in
                          let uu____27157 =
                            let uu____27162 =
                              let uu____27164 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____27166 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____27164 uu____27166
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____27162
                             in
                          (match uu____27157 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____27172 = attempt [prob] wl2  in
                               solve env uu____27172)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____27187 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____27187
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____27196 =
                                     let uu____27203 =
                                       let uu____27204 =
                                         let uu____27221 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____27224 =
                                           let uu____27235 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____27244 =
                                             let uu____27255 =
                                               let uu____27264 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____27264
                                                in
                                             [uu____27255]  in
                                           uu____27235 :: uu____27244  in
                                         (uu____27221, uu____27224)  in
                                       FStar_Syntax_Syntax.Tm_app uu____27204
                                        in
                                     FStar_Syntax_Syntax.mk uu____27203  in
                                   uu____27196 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____27313 =
                                    let uu____27320 =
                                      let uu____27321 =
                                        let uu____27338 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____27341 =
                                          let uu____27352 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____27361 =
                                            let uu____27372 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____27381 =
                                              let uu____27392 =
                                                let uu____27401 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____27401
                                                 in
                                              [uu____27392]  in
                                            uu____27372 :: uu____27381  in
                                          uu____27352 :: uu____27361  in
                                        (uu____27338, uu____27341)  in
                                      FStar_Syntax_Syntax.Tm_app uu____27321
                                       in
                                    FStar_Syntax_Syntax.mk uu____27320  in
                                  uu____27313 FStar_Pervasives_Native.None r)
                              in
                           (let uu____27455 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____27455
                            then
                              let uu____27460 =
                                let uu____27462 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding
                                      true;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____27462
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____27460
                            else ());
                           (let uu____27467 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____27467 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____27476 =
                                    let uu____27479 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _27482  ->
                                         FStar_Pervasives_Native.Some _27482)
                                      uu____27479
                                     in
                                  solve_prob orig uu____27476 [] wl1  in
                                let uu____27483 = attempt [base_prob] wl2  in
                                solve env uu____27483))))
           in
        let uu____27484 = FStar_Util.physical_equality c1 c2  in
        if uu____27484
        then
          let uu____27487 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____27487
        else
          ((let uu____27491 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____27491
            then
              let uu____27496 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____27498 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____27496
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____27498
            else ());
           (let uu____27503 =
              let uu____27512 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____27515 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____27512, uu____27515)  in
            match uu____27503 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____27533),FStar_Syntax_Syntax.Total
                    (t2,uu____27535)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____27552 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____27552 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____27554,FStar_Syntax_Syntax.Total uu____27555) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____27574),FStar_Syntax_Syntax.Total
                    (t2,uu____27576)) ->
                     let uu____27593 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____27593 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____27596),FStar_Syntax_Syntax.GTotal
                    (t2,uu____27598)) ->
                     let uu____27615 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____27615 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____27618),FStar_Syntax_Syntax.GTotal
                    (t2,uu____27620)) ->
                     if
                       problem.FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.SUB
                     then
                       let uu____27638 =
                         problem_using_guard orig t1
                           problem.FStar_TypeChecker_Common.relation t2
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____27638 wl
                     else giveup env "GTot =/= Tot" orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____27643,FStar_Syntax_Syntax.Comp uu____27644) ->
                     let uu____27653 =
                       let uu___3603_27656 = problem  in
                       let uu____27659 =
                         let uu____27660 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27660
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3603_27656.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____27659;
                         FStar_TypeChecker_Common.relation =
                           (uu___3603_27656.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3603_27656.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3603_27656.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3603_27656.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3603_27656.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3603_27656.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3603_27656.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3603_27656.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____27653 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____27661,FStar_Syntax_Syntax.Comp uu____27662) ->
                     let uu____27671 =
                       let uu___3603_27674 = problem  in
                       let uu____27677 =
                         let uu____27678 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27678
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3603_27674.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____27677;
                         FStar_TypeChecker_Common.relation =
                           (uu___3603_27674.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3603_27674.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3603_27674.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3603_27674.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3603_27674.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3603_27674.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3603_27674.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3603_27674.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____27671 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____27679,FStar_Syntax_Syntax.GTotal uu____27680) ->
                     let uu____27689 =
                       let uu___3615_27692 = problem  in
                       let uu____27695 =
                         let uu____27696 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27696
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3615_27692.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3615_27692.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3615_27692.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____27695;
                         FStar_TypeChecker_Common.element =
                           (uu___3615_27692.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3615_27692.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3615_27692.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3615_27692.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3615_27692.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3615_27692.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____27689 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____27697,FStar_Syntax_Syntax.Total uu____27698) ->
                     let uu____27707 =
                       let uu___3615_27710 = problem  in
                       let uu____27713 =
                         let uu____27714 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27714
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3615_27710.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3615_27710.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3615_27710.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____27713;
                         FStar_TypeChecker_Common.element =
                           (uu___3615_27710.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3615_27710.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3615_27710.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3615_27710.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3615_27710.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3615_27710.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____27707 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____27715,FStar_Syntax_Syntax.Comp uu____27716) ->
                     let uu____27717 =
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
                     if uu____27717
                     then
                       let uu____27720 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____27720 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____27727 =
                            let uu____27732 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____27732
                            then (c1_comp, c2_comp)
                            else
                              (let uu____27741 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____27742 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____27741, uu____27742))
                             in
                          match uu____27727 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11
                              in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21
                              in
                           (let uu____27750 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____27750
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____27758 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____27758 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____27761 =
                                  let uu____27763 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____27765 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____27763 uu____27765
                                   in
                                giveup env uu____27761 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____27776 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____27776 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____27826 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____27826 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____27851 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____27882  ->
                match uu____27882 with
                | (u1,u2) ->
                    let uu____27890 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____27892 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____27890 uu____27892))
         in
      FStar_All.pipe_right uu____27851 (FStar_String.concat ", ")  in
    FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1
  
let (guard_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun env  ->
    fun g  ->
      match ((g.FStar_TypeChecker_Env.guard_f),
              (g.FStar_TypeChecker_Env.deferred),
              (g.FStar_TypeChecker_Env.univ_ineqs))
      with
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____27929,[])) when
          let uu____27956 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____27956 -> "{}"
      | uu____27959 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____27986 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____27986
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____27998 =
              FStar_List.map
                (fun uu____28011  ->
                   match uu____28011 with
                   | (uu____28018,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____27998 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____28029 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____28029 imps
  
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
                  let uu____28086 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____28086
                  then
                    let uu____28094 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____28096 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____28094
                      (rel_to_string rel) uu____28096
                  else "TOP"  in
                let uu____28102 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____28102 with
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
              let uu____28162 =
                let uu____28165 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _28168  -> FStar_Pervasives_Native.Some _28168)
                  uu____28165
                 in
              FStar_Syntax_Syntax.new_bv uu____28162 t1  in
            let uu____28169 =
              let uu____28174 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____28174
               in
            match uu____28169 with | (p,wl1) -> (p, x, wl1)
  
let (solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob * Prims.string) ->
         (FStar_TypeChecker_Common.deferred *
           FStar_TypeChecker_Env.implicits) FStar_Pervasives_Native.option)
        ->
        (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun probs  ->
      fun err  ->
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        (let uu____28234 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____28234
         then
           let uu____28239 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____28239
         else ());
        (let uu____28246 =
           FStar_Util.record_time (fun uu____28253  -> solve env probs)  in
         match uu____28246 with
         | (sol,ms) ->
             ((let uu____28265 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____28265
               then
                 let uu____28270 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____28270
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____28283 =
                     FStar_Util.record_time
                       (fun uu____28290  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____28283 with
                    | ((),ms1) ->
                        ((let uu____28301 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____28301
                          then
                            let uu____28306 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____28306
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____28320 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____28320
                     then
                       let uu____28327 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____28327
                     else ());
                    (let result = err (d, s)  in
                     FStar_Syntax_Unionfind.rollback tx; result)))))
  
let (simplify_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____28354 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____28354
            then
              let uu____28359 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____28359
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding true;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____28367 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____28367
             then
               let uu____28372 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____28372
             else ());
            (let f2 =
               let uu____28378 =
                 let uu____28379 = FStar_Syntax_Util.unmeta f1  in
                 uu____28379.FStar_Syntax_Syntax.n  in
               match uu____28378 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____28383 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3731_28384 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___3731_28384.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___3731_28384.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___3731_28384.FStar_TypeChecker_Env.implicits)
             })))
  
let (with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicit
        Prims.list) FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred,implicits) ->
            let uu____28439 =
              let uu____28440 =
                let uu____28441 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _28442  ->
                       FStar_TypeChecker_Common.NonTrivial _28442)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____28441;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____28440  in
            FStar_All.pipe_left
              (fun _28449  -> FStar_Pervasives_Native.Some _28449)
              uu____28439
  
let with_guard_no_simp :
  'Auu____28459 .
    'Auu____28459 ->
      FStar_TypeChecker_Common.prob ->
        FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some d ->
            let uu____28482 =
              let uu____28483 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _28484  -> FStar_TypeChecker_Common.NonTrivial _28484)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____28483;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____28482
  
let (try_teq :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun smt_ok  ->
    fun env  ->
      fun t1  ->
        fun t2  ->
          (let uu____28517 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____28517
           then
             let uu____28522 = FStar_Syntax_Print.term_to_string t1  in
             let uu____28524 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____28522
               uu____28524
           else ());
          (let uu____28529 =
             let uu____28534 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____28534
              in
           match uu____28529 with
           | (prob,wl) ->
               let g =
                 let uu____28542 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____28552  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____28542  in
               ((let uu____28573 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____28573
                 then
                   let uu____28578 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____28578
                 else ());
                g))
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____28599 = try_teq true env t1 t2  in
        match uu____28599 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____28604 = FStar_TypeChecker_Env.get_range env  in
              let uu____28605 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____28604 uu____28605);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____28613 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____28613
              then
                let uu____28618 = FStar_Syntax_Print.term_to_string t1  in
                let uu____28620 = FStar_Syntax_Print.term_to_string t2  in
                let uu____28622 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____28618
                  uu____28620 uu____28622
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
          let uu____28648 = FStar_TypeChecker_Env.get_range env  in
          let uu____28649 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____28648 uu____28649
  
let (sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let rel =
          if env.FStar_TypeChecker_Env.use_eq
          then FStar_TypeChecker_Common.EQ
          else FStar_TypeChecker_Common.SUB  in
        (let uu____28678 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____28678
         then
           let uu____28683 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____28685 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____28683 uu____28685
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____28696 =
           let uu____28703 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____28703 "sub_comp"
            in
         match uu____28696 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____28716 =
                 FStar_Util.record_time
                   (fun uu____28728  ->
                      let uu____28729 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____28740  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____28729)
                  in
               match uu____28716 with
               | (r,ms) ->
                   ((let uu____28771 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____28771
                     then
                       let uu____28776 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____28778 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____28780 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____28776 uu____28778
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____28780
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
      fun uu____28818  ->
        match uu____28818 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____28861 =
                 let uu____28867 =
                   let uu____28869 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____28871 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____28869 uu____28871
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____28867)  in
               let uu____28875 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____28861 uu____28875)
               in
            let equiv1 v1 v' =
              let uu____28888 =
                let uu____28893 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____28894 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____28893, uu____28894)  in
              match uu____28888 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____28914 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____28945 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____28945 with
                      | FStar_Syntax_Syntax.U_unif uu____28952 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____28981  ->
                                    match uu____28981 with
                                    | (u,v') ->
                                        let uu____28990 = equiv1 v1 v'  in
                                        if uu____28990
                                        then
                                          let uu____28995 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____28995 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____29016 -> []))
               in
            let uu____29021 =
              let wl =
                let uu___3824_29025 = empty_worklist env  in
                {
                  attempting = (uu___3824_29025.attempting);
                  wl_deferred = (uu___3824_29025.wl_deferred);
                  ctr = (uu___3824_29025.ctr);
                  defer_ok = false;
                  smt_ok = (uu___3824_29025.smt_ok);
                  umax_heuristic_ok = (uu___3824_29025.umax_heuristic_ok);
                  tcenv = (uu___3824_29025.tcenv);
                  wl_implicits = (uu___3824_29025.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____29044  ->
                      match uu____29044 with
                      | (lb,v1) ->
                          let uu____29051 =
                            solve_universe_eq (~- Prims.int_one) wl lb v1  in
                          (match uu____29051 with
                           | USolved wl1 -> ()
                           | uu____29054 -> fail1 lb v1)))
               in
            let rec check_ineq uu____29065 =
              match uu____29065 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____29077) -> true
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
                      uu____29101,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____29103,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____29114) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____29122,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____29131 -> false)
               in
            let uu____29137 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____29154  ->
                      match uu____29154 with
                      | (u,v1) ->
                          let uu____29162 = check_ineq (u, v1)  in
                          if uu____29162
                          then true
                          else
                            ((let uu____29170 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____29170
                              then
                                let uu____29175 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____29177 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____29175
                                  uu____29177
                              else ());
                             false)))
               in
            if uu____29137
            then ()
            else
              ((let uu____29187 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____29187
                then
                  ((let uu____29193 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____29193);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____29205 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____29205))
                else ());
               (let uu____29218 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____29218))
  
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
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun defer_ok  ->
    fun env  ->
      fun g  ->
        let fail1 uu____29292 =
          match uu____29292 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___3901_29318 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___3901_29318.attempting);
            wl_deferred = (uu___3901_29318.wl_deferred);
            ctr = (uu___3901_29318.ctr);
            defer_ok;
            smt_ok = (uu___3901_29318.smt_ok);
            umax_heuristic_ok = (uu___3901_29318.umax_heuristic_ok);
            tcenv = (uu___3901_29318.tcenv);
            wl_implicits = (uu___3901_29318.wl_implicits)
          }  in
        (let uu____29321 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____29321
         then
           let uu____29326 = FStar_Util.string_of_bool defer_ok  in
           let uu____29328 = wl_to_string wl  in
           let uu____29330 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____29326 uu____29328 uu____29330
         else ());
        (let g1 =
           let uu____29336 = solve_and_commit env wl fail1  in
           match uu____29336 with
           | FStar_Pervasives_Native.Some
               (uu____29343::uu____29344,uu____29345) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___3916_29374 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___3916_29374.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___3916_29374.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____29375 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___3921_29384 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___3921_29384.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___3921_29384.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___3921_29384.FStar_TypeChecker_Env.implicits)
          }))
  
let (solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints false env g 
let (solve_some_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints true env g 
let (discharge_guard' :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Env.guard_t ->
        Prims.bool ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
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
            let uu___3933_29461 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___3933_29461.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___3933_29461.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___3933_29461.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____29462 =
            let uu____29464 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____29464  in
          if uu____29462
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____29476 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____29477 =
                       let uu____29479 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____29479
                        in
                     FStar_Errors.diag uu____29476 uu____29477)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding true;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____29488 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____29489 =
                        let uu____29491 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____29491
                         in
                      FStar_Errors.diag uu____29488 uu____29489)
                   else ();
                   (let uu____29497 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____29497
                      "discharge_guard'" env vc1);
                   (let uu____29499 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____29499 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____29508 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____29509 =
                                let uu____29511 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____29511
                                 in
                              FStar_Errors.diag uu____29508 uu____29509)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____29521 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____29522 =
                                let uu____29524 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____29524
                                 in
                              FStar_Errors.diag uu____29521 uu____29522)
                           else ();
                           (let vcs =
                              let uu____29538 = FStar_Options.use_tactics ()
                                 in
                              if uu____29538
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____29560  ->
                                     (let uu____29562 =
                                        FStar_Options.set_options
                                          "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____29562);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____29606  ->
                                              match uu____29606 with
                                              | (env1,goal,opts) ->
                                                  let uu____29622 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____29622, opts)))))
                              else
                                (let uu____29625 =
                                   let uu____29632 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____29632)  in
                                 [uu____29625])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____29665  ->
                                    match uu____29665 with
                                    | (env1,goal,opts) ->
                                        let uu____29675 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____29675 with
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
                                                (let uu____29686 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____29687 =
                                                   let uu____29689 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____29691 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____29689 uu____29691
                                                    in
                                                 FStar_Errors.diag
                                                   uu____29686 uu____29687)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____29698 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____29699 =
                                                   let uu____29701 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____29701
                                                    in
                                                 FStar_Errors.diag
                                                   uu____29698 uu____29699)
                                              else ();
                                              (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                                use_env_range_msg env1 goal1;
                                              FStar_Options.pop ())))));
                           FStar_Pervasives_Native.Some ret_g)))))
  
let (discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____29719 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____29719 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____29728 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____29728
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____29742 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____29742 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____29772 = try_teq false env t1 t2  in
        match uu____29772 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some g ->
            discharge_guard' FStar_Pervasives_Native.None env g false
  
let (resolve_implicits' :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      Prims.bool ->
        FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun must_total  ->
      fun forcelax  ->
        fun g  ->
          let rec unresolved ctx_u =
            let uu____29816 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____29816 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____29829 ->
                     let uu____29842 =
                       let uu____29843 = FStar_Syntax_Subst.compress r  in
                       uu____29843.FStar_Syntax_Syntax.n  in
                     (match uu____29842 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____29848) ->
                          unresolved ctx_u'
                      | uu____29865 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____29889 = acc  in
            match uu____29889 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____29908 = hd1  in
                     (match uu____29908 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____29919 = unresolved ctx_u  in
                             if uu____29919
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____29943 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____29943
                                     then
                                       let uu____29947 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____29947
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____29956 = teq_nosmt env1 t tm
                                          in
                                       match uu____29956 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Env.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4045_29966 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4045_29966.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4045_29966.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4045_29966.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4045_29966.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4045_29966.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4045_29966.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4045_29966.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4048_29974 = hd1  in
                                       {
                                         FStar_TypeChecker_Env.imp_reason =
                                           (uu___4048_29974.FStar_TypeChecker_Env.imp_reason);
                                         FStar_TypeChecker_Env.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Env.imp_tm =
                                           (uu___4048_29974.FStar_TypeChecker_Env.imp_tm);
                                         FStar_TypeChecker_Env.imp_range =
                                           (uu___4048_29974.FStar_TypeChecker_Env.imp_range)
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
                                    let uu___4052_29985 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4052_29985.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4052_29985.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4052_29985.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4052_29985.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4052_29985.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4052_29985.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4052_29985.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4052_29985.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4052_29985.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___4052_29985.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4052_29985.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4052_29985.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4052_29985.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4052_29985.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4052_29985.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4052_29985.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4052_29985.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4052_29985.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4052_29985.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4052_29985.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4052_29985.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4052_29985.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4052_29985.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4052_29985.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4052_29985.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4052_29985.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4052_29985.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4052_29985.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4052_29985.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4052_29985.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4052_29985.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4052_29985.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4052_29985.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4052_29985.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4052_29985.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4052_29985.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4052_29985.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4052_29985.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4052_29985.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4052_29985.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4052_29985.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4052_29985.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4052_29985.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4052_29985.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4057_29989 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4057_29989.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4057_29989.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4057_29989.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4057_29989.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4057_29989.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4057_29989.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4057_29989.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4057_29989.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4057_29989.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4057_29989.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___4057_29989.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4057_29989.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4057_29989.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4057_29989.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4057_29989.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4057_29989.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4057_29989.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4057_29989.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4057_29989.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4057_29989.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4057_29989.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4057_29989.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4057_29989.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4057_29989.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4057_29989.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4057_29989.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4057_29989.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4057_29989.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4057_29989.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4057_29989.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4057_29989.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4057_29989.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4057_29989.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4057_29989.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4057_29989.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4057_29989.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4057_29989.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4057_29989.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4057_29989.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4057_29989.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4057_29989.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4057_29989.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4057_29989.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4057_29989.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____29994 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____29994
                                   then
                                     let uu____29999 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____30001 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____30003 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____30005 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____29999 uu____30001 uu____30003
                                       reason uu____30005
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4063_30012  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____30019 =
                                             let uu____30029 =
                                               let uu____30037 =
                                                 let uu____30039 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____30041 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____30043 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____30039 uu____30041
                                                   uu____30043
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____30037, r)
                                                in
                                             [uu____30029]  in
                                           FStar_Errors.add_errors
                                             uu____30019);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___4071_30063 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___4071_30063.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___4071_30063.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___4071_30063.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____30067 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____30078  ->
                                               let uu____30079 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____30081 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____30083 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____30079 uu____30081
                                                 reason uu____30083)) env2 g2
                                         true
                                        in
                                     match uu____30067 with
                                     | FStar_Pervasives_Native.Some g3 -> g3
                                     | FStar_Pervasives_Native.None  ->
                                         failwith
                                           "Impossible, with use_smt = true, discharge_guard' should never have returned None"
                                      in
                                   until_fixpoint
                                     ((FStar_List.append
                                         g'.FStar_TypeChecker_Env.implicits
                                         out), true) tl1)))))
             in
          let uu___4079_30091 = g  in
          let uu____30092 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4079_30091.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4079_30091.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___4079_30091.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____30092
          }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      resolve_implicits' env
        ((Prims.op_Negation env.FStar_TypeChecker_Env.phase1) &&
           (Prims.op_Negation env.FStar_TypeChecker_Env.lax)) false g
  
let (resolve_implicits_tac :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun env  -> fun g  -> resolve_implicits' env false true g 
let (force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> unit) =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____30134 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____30134 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____30135 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____30135
      | imp::uu____30137 ->
          let uu____30140 =
            let uu____30146 =
              let uu____30148 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____30150 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____30148 uu____30150 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____30146)
             in
          FStar_Errors.raise_error uu____30140
            imp.FStar_TypeChecker_Env.imp_range
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____30172 = teq_nosmt env t1 t2  in
        match uu____30172 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4101_30191 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___4101_30191.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___4101_30191.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___4101_30191.FStar_TypeChecker_Env.implicits)
      }
  
let (check_subtyping :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv * FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____30227 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30227
         then
           let uu____30232 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____30234 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____30232
             uu____30234
         else ());
        (let uu____30239 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____30239 with
         | (prob,x,wl) ->
             let g =
               let uu____30258 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30269  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30258  in
             ((let uu____30290 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____30290
               then
                 let uu____30295 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____30297 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____30299 =
                   let uu____30301 = FStar_Util.must g  in
                   guard_to_string env uu____30301  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____30295 uu____30297 uu____30299
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
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____30338 = check_subtyping env t1 t2  in
        match uu____30338 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____30357 =
              let uu____30358 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____30358 g  in
            FStar_Pervasives_Native.Some uu____30357
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____30377 = check_subtyping env t1 t2  in
        match uu____30377 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____30396 =
              let uu____30397 =
                let uu____30398 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____30398]  in
              FStar_TypeChecker_Env.close_guard env uu____30397 g  in
            FStar_Pervasives_Native.Some uu____30396
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____30436 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30436
         then
           let uu____30441 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____30443 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____30441
             uu____30443
         else ());
        (let uu____30448 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____30448 with
         | (prob,x,wl) ->
             let g =
               let uu____30463 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____30474  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30463  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____30498 =
                      let uu____30499 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____30499]  in
                    FStar_TypeChecker_Env.close_guard env uu____30498 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____30540 = subtype_nosmt env t1 t2  in
        match uu____30540 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  