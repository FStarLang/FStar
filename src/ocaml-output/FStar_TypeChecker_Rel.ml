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
              FStar_TypeChecker_Env.mpreprocess =
                (uu___77_569.FStar_TypeChecker_Env.mpreprocess);
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
                                (uu___2970_21066.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___2970_21066.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___2970_21066.FStar_TypeChecker_Env.mpreprocess);
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
                                (uu___2970_21405.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___2970_21405.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___2970_21405.FStar_TypeChecker_Env.mpreprocess);
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
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____26303 =
                  let uu____26305 =
                    FStar_Syntax_Print.args_to_string
                      c1_comp.FStar_Syntax_Syntax.effect_args
                     in
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
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____26519 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____26519
           then
             let uu____26524 =
               let uu____26526 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26526
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____26528 =
               let uu____26530 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26530
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____26524 uu____26528
           else ());
          (let uu____26535 =
             let uu____26540 =
               let uu____26545 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26545
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____26540
               (fun uu____26562  ->
                  match uu____26562 with
                  | (c,g) ->
                      let uu____26573 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____26573, g))
              in
           match uu____26535 with
           | (c12,g_lift) ->
               ((let uu____26577 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____26577
                 then
                   let uu____26582 =
                     let uu____26584 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26584
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____26586 =
                     let uu____26588 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26588
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____26582 uu____26586
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3485_26598 = wl  in
                     {
                       attempting = (uu___3485_26598.attempting);
                       wl_deferred = (uu___3485_26598.wl_deferred);
                       ctr = (uu___3485_26598.ctr);
                       defer_ok = (uu___3485_26598.defer_ok);
                       smt_ok = (uu___3485_26598.smt_ok);
                       umax_heuristic_ok =
                         (uu___3485_26598.umax_heuristic_ok);
                       tcenv = (uu___3485_26598.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
                   let uu____26599 =
                     let is_uvar1 t =
                       let uu____26613 =
                         let uu____26614 = FStar_Syntax_Subst.compress t  in
                         uu____26614.FStar_Syntax_Syntax.n  in
                       match uu____26613 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____26618 -> true
                       | FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_uvar uu____26632;
                              FStar_Syntax_Syntax.pos = uu____26633;
                              FStar_Syntax_Syntax.vars = uu____26634;_},uu____26635)
                           -> true
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_uvar uu____26653;
                              FStar_Syntax_Syntax.pos = uu____26654;
                              FStar_Syntax_Syntax.vars = uu____26655;_},uu____26656)
                           -> true
                       | uu____26694 -> false  in
                     FStar_List.fold_right2
                       (fun uu____26727  ->
                          fun uu____26728  ->
                            fun uu____26729  ->
                              match (uu____26727, uu____26728, uu____26729)
                              with
                              | ((a1,uu____26773),(a2,uu____26775),(is_sub_probs,wl2))
                                  ->
                                  let uu____26808 = is_uvar1 a1  in
                                  if uu____26808
                                  then
                                    let uu____26817 =
                                      sub_prob wl2 a1
                                        FStar_TypeChecker_Common.EQ a2
                                        "l.h.s. effect index uvar"
                                       in
                                    (match uu____26817 with
                                     | (p,wl3) -> ((p :: is_sub_probs), wl3))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____26599 with
                   | (is_sub_probs,wl2) ->
                       let uu____26845 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____26845 with
                        | (ret_sub_prob,wl3) ->
                            let uu____26853 =
                              let uu____26858 =
                                let uu____26859 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____26859
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____26858
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____26853 with
                             | (uu____26866,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____26877 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____26879 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____26877 s uu____26879
                                    in
                                 let uu____26882 =
                                   let uu____26911 =
                                     let uu____26912 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____26912.FStar_Syntax_Syntax.n  in
                                   match uu____26911 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____26972 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____26972 with
                                        | (a::bs1,c3) ->
                                            let uu____27028 =
                                              let uu____27047 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27047
                                                (fun uu____27151  ->
                                                   match uu____27151 with
                                                   | (l1,l2) ->
                                                       let uu____27224 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____27224))
                                               in
                                            (match uu____27028 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____27329 ->
                                       let uu____27330 =
                                         let uu____27336 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____27336)
                                          in
                                       FStar_Errors.raise_error uu____27330 r
                                    in
                                 (match uu____26882 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____27412 =
                                        let uu____27419 =
                                          let uu____27420 =
                                            let uu____27421 =
                                              let uu____27428 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____27428,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____27421
                                             in
                                          [uu____27420]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____27419
                                          (fun b  ->
                                             let uu____27444 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____27446 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____27448 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____27444 uu____27446
                                               uu____27448) r
                                         in
                                      (match uu____27412 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           let wl4 =
                                             let uu___3559_27458 = wl3  in
                                             {
                                               attempting =
                                                 (uu___3559_27458.attempting);
                                               wl_deferred =
                                                 (uu___3559_27458.wl_deferred);
                                               ctr = (uu___3559_27458.ctr);
                                               defer_ok =
                                                 (uu___3559_27458.defer_ok);
                                               smt_ok =
                                                 (uu___3559_27458.smt_ok);
                                               umax_heuristic_ok =
                                                 (uu___3559_27458.umax_heuristic_ok);
                                               tcenv =
                                                 (uu___3559_27458.tcenv);
                                               wl_implicits =
                                                 (FStar_List.append
                                                    g_uvars.FStar_TypeChecker_Common.implicits
                                                    wl3.wl_implicits)
                                             }  in
                                           let substs =
                                             FStar_List.map2
                                               (fun b  ->
                                                  fun t  ->
                                                    let uu____27483 =
                                                      let uu____27490 =
                                                        FStar_All.pipe_right
                                                          b
                                                          FStar_Pervasives_Native.fst
                                                         in
                                                      (uu____27490, t)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____27483) (a_b ::
                                               rest_bs)
                                               ((c21.FStar_Syntax_Syntax.result_typ)
                                               :: rest_bs_uvars)
                                              in
                                           let uu____27507 =
                                             let f_sort_is =
                                               let uu____27517 =
                                                 let uu____27518 =
                                                   let uu____27521 =
                                                     let uu____27522 =
                                                       FStar_All.pipe_right
                                                         f_b
                                                         FStar_Pervasives_Native.fst
                                                        in
                                                     uu____27522.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Subst.compress
                                                     uu____27521
                                                    in
                                                 uu____27518.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____27517 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____27533,uu____27534::is)
                                                   ->
                                                   let uu____27576 =
                                                     FStar_All.pipe_right is
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____27576
                                                     (FStar_List.map
                                                        (FStar_Syntax_Subst.subst
                                                           substs))
                                               | uu____27609 ->
                                                   let uu____27610 =
                                                     let uu____27616 =
                                                       stronger_t_shape_error
                                                         "type of f is not a repr type"
                                                        in
                                                     (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                       uu____27616)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____27610 r
                                                in
                                             let uu____27622 =
                                               FStar_All.pipe_right
                                                 c12.FStar_Syntax_Syntax.effect_args
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_List.fold_left2
                                               (fun uu____27657  ->
                                                  fun f_sort_i  ->
                                                    fun c1_i  ->
                                                      match uu____27657 with
                                                      | (ps,wl5) ->
                                                          let uu____27678 =
                                                            sub_prob wl5
                                                              f_sort_i
                                                              FStar_TypeChecker_Common.EQ
                                                              c1_i
                                                              "indices of c1"
                                                             in
                                                          (match uu____27678
                                                           with
                                                           | (p,wl6) ->
                                                               ((FStar_List.append
                                                                   ps 
                                                                   [p]), wl6)))
                                               ([], wl4) f_sort_is
                                               uu____27622
                                              in
                                           (match uu____27507 with
                                            | (f_sub_probs,wl5) ->
                                                let stronger_ct =
                                                  let uu____27703 =
                                                    FStar_All.pipe_right
                                                      stronger_c
                                                      (FStar_Syntax_Subst.subst_comp
                                                         substs)
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____27703
                                                    FStar_Syntax_Util.comp_to_comp_typ
                                                   in
                                                let uu____27704 =
                                                  let g_sort_is =
                                                    let uu____27714 =
                                                      let uu____27715 =
                                                        FStar_Syntax_Subst.compress
                                                          stronger_ct.FStar_Syntax_Syntax.result_typ
                                                         in
                                                      uu____27715.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____27714 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (uu____27720,uu____27721::is)
                                                        ->
                                                        FStar_All.pipe_right
                                                          is
                                                          (FStar_List.map
                                                             FStar_Pervasives_Native.fst)
                                                    | uu____27789 ->
                                                        let uu____27790 =
                                                          let uu____27796 =
                                                            stronger_t_shape_error
                                                              "return type is not a repr type"
                                                             in
                                                          (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                            uu____27796)
                                                           in
                                                        FStar_Errors.raise_error
                                                          uu____27790 r
                                                     in
                                                  let uu____27802 =
                                                    FStar_All.pipe_right
                                                      c21.FStar_Syntax_Syntax.effect_args
                                                      (FStar_List.map
                                                         FStar_Pervasives_Native.fst)
                                                     in
                                                  FStar_List.fold_left2
                                                    (fun uu____27837  ->
                                                       fun g_sort_i  ->
                                                         fun c2_i  ->
                                                           match uu____27837
                                                           with
                                                           | (ps,wl6) ->
                                                               let uu____27858
                                                                 =
                                                                 sub_prob wl6
                                                                   g_sort_i
                                                                   FStar_TypeChecker_Common.EQ
                                                                   c2_i
                                                                   "indices of c2"
                                                                  in
                                                               (match uu____27858
                                                                with
                                                                | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                    ([], wl5) g_sort_is
                                                    uu____27802
                                                   in
                                                (match uu____27704 with
                                                 | (g_sub_probs,wl6) ->
                                                     let fml =
                                                       let uu____27885 =
                                                         let uu____27890 =
                                                           FStar_List.hd
                                                             stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                            in
                                                         let uu____27891 =
                                                           let uu____27892 =
                                                             FStar_List.hd
                                                               stronger_ct.FStar_Syntax_Syntax.effect_args
                                                              in
                                                           FStar_Pervasives_Native.fst
                                                             uu____27892
                                                            in
                                                         (uu____27890,
                                                           uu____27891)
                                                          in
                                                       match uu____27885 with
                                                       | (u,wp) ->
                                                           let trivial_post =
                                                             let ts =
                                                               let uu____27919
                                                                 =
                                                                 FStar_TypeChecker_Env.lookup_definition
                                                                   [FStar_TypeChecker_Env.NoDelta]
                                                                   env
                                                                   FStar_Parser_Const.trivial_pure_post_lid
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____27919
                                                                 FStar_Util.must
                                                                in
                                                             let uu____27936
                                                               =
                                                               FStar_TypeChecker_Env.inst_tscheme_with
                                                                 ts [u]
                                                                in
                                                             match uu____27936
                                                             with
                                                             | (uu____27941,t)
                                                                 ->
                                                                 let uu____27943
                                                                   =
                                                                   let uu____27948
                                                                    =
                                                                    let uu____27949
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    stronger_ct.FStar_Syntax_Syntax.result_typ
                                                                    FStar_Syntax_Syntax.as_arg
                                                                     in
                                                                    [uu____27949]
                                                                     in
                                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                                    t
                                                                    uu____27948
                                                                    in
                                                                 uu____27943
                                                                   FStar_Pervasives_Native.None
                                                                   FStar_Range.dummyRange
                                                              in
                                                           let uu____27982 =
                                                             let uu____27987
                                                               =
                                                               let uu____27988
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   trivial_post
                                                                   FStar_Syntax_Syntax.as_arg
                                                                  in
                                                               [uu____27988]
                                                                in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               wp uu____27987
                                                              in
                                                           uu____27982
                                                             FStar_Pervasives_Native.None
                                                             FStar_Range.dummyRange
                                                        in
                                                     let sub_probs =
                                                       let uu____28024 =
                                                         let uu____28027 =
                                                           let uu____28030 =
                                                             let uu____28033
                                                               =
                                                               FStar_All.pipe_right
                                                                 g_lift.FStar_TypeChecker_Common.deferred
                                                                 (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                in
                                                             FStar_List.append
                                                               g_sub_probs
                                                               uu____28033
                                                              in
                                                           FStar_List.append
                                                             f_sub_probs
                                                             uu____28030
                                                            in
                                                         FStar_List.append
                                                           is_sub_probs
                                                           uu____28027
                                                          in
                                                       ret_sub_prob ::
                                                         uu____28024
                                                        in
                                                     let guard =
                                                       let guard =
                                                         let uu____28057 =
                                                           FStar_List.map
                                                             p_guard
                                                             sub_probs
                                                            in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____28057
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
                                                       let uu____28068 =
                                                         let uu____28071 =
                                                           FStar_Syntax_Util.mk_conj
                                                             guard fml
                                                            in
                                                         FStar_All.pipe_left
                                                           (fun _28074  ->
                                                              FStar_Pervasives_Native.Some
                                                                _28074)
                                                           uu____28071
                                                          in
                                                       solve_prob orig
                                                         uu____28068 [] wl6
                                                        in
                                                     let uu____28075 =
                                                       attempt sub_probs wl7
                                                        in
                                                     solve env uu____28075)))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28098 =
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28100 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28100]
              | x -> x  in
            let c12 =
              let uu___3630_28103 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs1;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3630_28103.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3630_28103.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3630_28103.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3630_28103.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28104 =
              let uu____28109 =
                FStar_All.pipe_right
                  (let uu___3633_28111 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs1;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3633_28111.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3633_28111.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3633_28111.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3633_28111.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28109
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28104
              (fun uu____28125  ->
                 match uu____28125 with
                 | (c,g) ->
                     let uu____28132 =
                       let uu____28134 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28134  in
                     if uu____28132
                     then
                       let uu____28137 =
                         let uu____28143 =
                           let uu____28145 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28147 =
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                             uu____28145 uu____28147
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28143)
                          in
                       FStar_Errors.raise_error uu____28137 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28153 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28153
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
              (let uu____28159 = lift_c1 ()  in
               solve_eq uu____28159 c21 FStar_TypeChecker_Env.trivial_guard)
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
                      (fun uu___31_28168  ->
                         match uu___31_28168 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28173 -> false))
                  in
               let uu____28175 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28205)::uu____28206,(wp2,uu____28208)::uu____28209)
                     -> (wp1, wp2)
                 | uu____28282 ->
                     let uu____28307 =
                       let uu____28313 =
                         let uu____28315 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____28317 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____28315 uu____28317
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____28313)
                        in
                     FStar_Errors.raise_error uu____28307
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28175 with
               | (wpc1,wpc2) ->
                   let uu____28327 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____28327
                   then
                     let uu____28330 =
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28330 wl
                   else
                     (let uu____28334 =
                        let uu____28341 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____28341  in
                      match uu____28334 with
                      | (c2_decl,qualifiers) ->
                          let uu____28362 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____28362
                          then
                            let c1_repr =
                              let uu____28369 =
                                let uu____28370 =
                                  let uu____28371 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____28371  in
                                let uu____28372 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28370 uu____28372
                                 in
                              FStar_TypeChecker_Normalize.normalize
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28369
                               in
                            let c2_repr =
                              let uu____28374 =
                                let uu____28375 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____28376 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28375 uu____28376
                                 in
                              FStar_TypeChecker_Normalize.normalize
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28374
                               in
                            let uu____28377 =
                              let uu____28382 =
                                let uu____28384 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____28386 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____28384
                                  uu____28386
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____28382
                               in
                            (match uu____28377 with
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
                                 let uu____28392 = attempt [prob] wl2  in
                                 solve env uu____28392)
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
                               else
                                 (let wpc1_2 =
                                    let uu____28412 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____28412
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  if is_null_wp_2
                                  then
                                    ((let uu____28435 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____28435
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
                                        let uu____28445 =
                                          FStar_All.pipe_right c2_decl
                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                           in
                                        match uu____28445 with
                                        | FStar_Pervasives_Native.None  ->
                                            failwith
                                              "Rel doesn't yet handle undefined trivial combinator in an effect"
                                        | FStar_Pervasives_Native.Some t -> t
                                         in
                                      let uu____28452 =
                                        let uu____28459 =
                                          let uu____28460 =
                                            let uu____28477 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____28480 =
                                              let uu____28491 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____28491; wpc1_2]  in
                                            (uu____28477, uu____28480)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____28460
                                           in
                                        FStar_Syntax_Syntax.mk uu____28459
                                         in
                                      uu____28452
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
                                     let uu____28540 =
                                       let uu____28547 =
                                         let uu____28548 =
                                           let uu____28565 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____28568 =
                                             let uu____28579 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____28588 =
                                               let uu____28599 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____28599; wpc1_2]  in
                                             uu____28579 :: uu____28588  in
                                           (uu____28565, uu____28568)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____28548
                                          in
                                       FStar_Syntax_Syntax.mk uu____28547  in
                                     uu____28540 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____28653 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____28653
                              then
                                let uu____28658 =
                                  let uu____28660 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
                                    uu____28660
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____28658
                              else ());
                             (let uu____28664 =
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
                              match uu____28664 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____28673 =
                                      let uu____28676 =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
                                        (fun _28679  ->
                                           FStar_Pervasives_Native.Some
                                             _28679) uu____28676
                                       in
                                    solve_prob orig uu____28673 [] wl1  in
                                  let uu____28680 = attempt [base_prob] wl2
                                     in
                                  solve env uu____28680))))
           in
        let uu____28681 = FStar_Util.physical_equality c1 c2  in
        if uu____28681
        then
          let uu____28684 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____28684
        else
          ((let uu____28688 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____28688
            then
              let uu____28693 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____28695 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____28693
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____28695
            else ());
           (let uu____28700 =
              let uu____28709 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____28712 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____28709, uu____28712)  in
            match uu____28700 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____28730),FStar_Syntax_Syntax.Total
                    (t2,uu____28732)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____28749 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28749 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____28751,FStar_Syntax_Syntax.Total uu____28752) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____28771),FStar_Syntax_Syntax.Total
                    (t2,uu____28773)) ->
                     let uu____28790 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28790 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____28793),FStar_Syntax_Syntax.GTotal
                    (t2,uu____28795)) ->
                     let uu____28812 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28812 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____28815),FStar_Syntax_Syntax.GTotal
                    (t2,uu____28817)) ->
                     if
                       problem.FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.SUB
                     then
                       let uu____28835 =
                         problem_using_guard orig t1
                           problem.FStar_TypeChecker_Common.relation t2
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____28835 wl
                     else giveup env "GTot =/= Tot" orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____28840,FStar_Syntax_Syntax.Comp uu____28841) ->
                     let uu____28850 =
                       let uu___3749_28853 = problem  in
                       let uu____28856 =
                         let uu____28857 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____28857
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3749_28853.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____28856;
                         FStar_TypeChecker_Common.relation =
                           (uu___3749_28853.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3749_28853.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3749_28853.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3749_28853.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3749_28853.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3749_28853.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3749_28853.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3749_28853.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____28850 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____28858,FStar_Syntax_Syntax.Comp uu____28859) ->
                     let uu____28868 =
                       let uu___3749_28871 = problem  in
                       let uu____28874 =
                         let uu____28875 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____28875
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3749_28871.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____28874;
                         FStar_TypeChecker_Common.relation =
                           (uu___3749_28871.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3749_28871.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3749_28871.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3749_28871.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3749_28871.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3749_28871.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3749_28871.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3749_28871.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____28868 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____28876,FStar_Syntax_Syntax.GTotal uu____28877) ->
                     let uu____28886 =
                       let uu___3761_28889 = problem  in
                       let uu____28892 =
                         let uu____28893 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____28893
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3761_28889.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3761_28889.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3761_28889.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____28892;
                         FStar_TypeChecker_Common.element =
                           (uu___3761_28889.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3761_28889.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3761_28889.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3761_28889.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3761_28889.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3761_28889.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____28886 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____28894,FStar_Syntax_Syntax.Total uu____28895) ->
                     let uu____28904 =
                       let uu___3761_28907 = problem  in
                       let uu____28910 =
                         let uu____28911 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____28911
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3761_28907.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3761_28907.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3761_28907.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____28910;
                         FStar_TypeChecker_Common.element =
                           (uu___3761_28907.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3761_28907.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3761_28907.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3761_28907.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3761_28907.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3761_28907.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____28904 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____28912,FStar_Syntax_Syntax.Comp uu____28913) ->
                     let uu____28914 =
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
                     if uu____28914
                     then
                       let uu____28917 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____28917 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____28924 =
                            let uu____28929 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____28929
                            then (c1_comp, c2_comp)
                            else
                              (let uu____28938 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____28939 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____28938, uu____28939))
                             in
                          match uu____28924 with
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
                           (let uu____28947 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____28947
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____28955 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____28955 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____28958 =
                                  let uu____28960 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____28962 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____28960 uu____28962
                                   in
                                giveup env uu____28958 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____28973 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____28973 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29023 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29023 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29048 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29079  ->
                match uu____29079 with
                | (u1,u2) ->
                    let uu____29087 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29089 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29087 uu____29089))
         in
      FStar_All.pipe_right uu____29048 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29126,[])) when
          let uu____29153 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29153 -> "{}"
      | uu____29156 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29183 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29183
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____29195 =
              FStar_List.map
                (fun uu____29208  ->
                   match uu____29208 with
                   | (uu____29215,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Common.deferred
               in
            FStar_All.pipe_right uu____29195 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____29226 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____29226 imps
  
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
                  let uu____29283 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____29283
                  then
                    let uu____29291 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____29293 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____29291
                      (rel_to_string rel) uu____29293
                  else "TOP"  in
                let uu____29299 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____29299 with
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
              let uu____29359 =
                let uu____29362 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _29365  -> FStar_Pervasives_Native.Some _29365)
                  uu____29362
                 in
              FStar_Syntax_Syntax.new_bv uu____29359 t1  in
            let uu____29366 =
              let uu____29371 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____29371
               in
            match uu____29366 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____29431 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____29431
         then
           let uu____29436 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____29436
         else ());
        (let uu____29443 =
           FStar_Util.record_time (fun uu____29450  -> solve env probs)  in
         match uu____29443 with
         | (sol,ms) ->
             ((let uu____29462 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____29462
               then
                 let uu____29467 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____29467
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____29480 =
                     FStar_Util.record_time
                       (fun uu____29487  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____29480 with
                    | ((),ms1) ->
                        ((let uu____29498 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____29498
                          then
                            let uu____29503 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____29503
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____29517 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____29517
                     then
                       let uu____29524 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____29524
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
          ((let uu____29551 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____29551
            then
              let uu____29556 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____29556
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____29563 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____29563
             then
               let uu____29568 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____29568
             else ());
            (let f2 =
               let uu____29574 =
                 let uu____29575 = FStar_Syntax_Util.unmeta f1  in
                 uu____29575.FStar_Syntax_Syntax.n  in
               match uu____29574 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____29579 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3877_29580 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred =
                 (uu___3877_29580.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___3877_29580.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___3877_29580.FStar_TypeChecker_Common.implicits)
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
            let uu____29623 =
              let uu____29624 =
                let uu____29625 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _29626  ->
                       FStar_TypeChecker_Common.NonTrivial _29626)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____29625;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____29624  in
            FStar_All.pipe_left
              (fun _29633  -> FStar_Pervasives_Native.Some _29633)
              uu____29623
  
let with_guard_no_simp :
  'Auu____29643 .
    'Auu____29643 ->
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
            let uu____29666 =
              let uu____29667 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _29668  -> FStar_TypeChecker_Common.NonTrivial _29668)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____29667;
                FStar_TypeChecker_Common.deferred = d;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____29666
  
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
          (let uu____29701 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____29701
           then
             let uu____29706 = FStar_Syntax_Print.term_to_string t1  in
             let uu____29708 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____29706
               uu____29708
           else ());
          (let uu____29713 =
             let uu____29718 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____29718
              in
           match uu____29713 with
           | (prob,wl) ->
               let g =
                 let uu____29726 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____29734  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____29726  in
               ((let uu____29753 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____29753
                 then
                   let uu____29758 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____29758
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
        let uu____29779 = try_teq true env t1 t2  in
        match uu____29779 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____29784 = FStar_TypeChecker_Env.get_range env  in
              let uu____29785 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____29784 uu____29785);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____29793 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____29793
              then
                let uu____29798 = FStar_Syntax_Print.term_to_string t1  in
                let uu____29800 = FStar_Syntax_Print.term_to_string t2  in
                let uu____29802 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____29798
                  uu____29800 uu____29802
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
          let uu____29828 = FStar_TypeChecker_Env.get_range env  in
          let uu____29829 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____29828 uu____29829
  
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
        (let uu____29858 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____29858
         then
           let uu____29863 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____29865 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____29863 uu____29865
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____29876 =
           let uu____29883 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____29883 "sub_comp"
            in
         match uu____29876 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____29896 =
                 FStar_Util.record_time
                   (fun uu____29908  ->
                      let uu____29909 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____29918  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____29909)
                  in
               match uu____29896 with
               | (r,ms) ->
                   ((let uu____29947 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____29947
                     then
                       let uu____29952 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____29954 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____29956 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____29952 uu____29954
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____29956
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
      fun uu____29994  ->
        match uu____29994 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____30037 =
                 let uu____30043 =
                   let uu____30045 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____30047 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____30045 uu____30047
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____30043)  in
               let uu____30051 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____30037 uu____30051)
               in
            let equiv1 v1 v' =
              let uu____30064 =
                let uu____30069 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____30070 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____30069, uu____30070)  in
              match uu____30064 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____30090 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____30121 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____30121 with
                      | FStar_Syntax_Syntax.U_unif uu____30128 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____30157  ->
                                    match uu____30157 with
                                    | (u,v') ->
                                        let uu____30166 = equiv1 v1 v'  in
                                        if uu____30166
                                        then
                                          let uu____30171 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____30171 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____30192 -> []))
               in
            let uu____30197 =
              let wl =
                let uu___3970_30201 = empty_worklist env  in
                {
                  attempting = (uu___3970_30201.attempting);
                  wl_deferred = (uu___3970_30201.wl_deferred);
                  ctr = (uu___3970_30201.ctr);
                  defer_ok = false;
                  smt_ok = (uu___3970_30201.smt_ok);
                  umax_heuristic_ok = (uu___3970_30201.umax_heuristic_ok);
                  tcenv = (uu___3970_30201.tcenv);
                  wl_implicits = (uu___3970_30201.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____30220  ->
                      match uu____30220 with
                      | (lb,v1) ->
                          let uu____30227 =
                            solve_universe_eq (~- Prims.int_one) wl lb v1  in
                          (match uu____30227 with
                           | USolved wl1 -> ()
                           | uu____30230 -> fail1 lb v1)))
               in
            let rec check_ineq uu____30241 =
              match uu____30241 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____30253) -> true
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
                      uu____30277,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____30279,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____30290) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____30298,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____30307 -> false)
               in
            let uu____30313 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____30330  ->
                      match uu____30330 with
                      | (u,v1) ->
                          let uu____30338 = check_ineq (u, v1)  in
                          if uu____30338
                          then true
                          else
                            ((let uu____30346 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____30346
                              then
                                let uu____30351 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____30353 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____30351
                                  uu____30353
                              else ());
                             false)))
               in
            if uu____30313
            then ()
            else
              ((let uu____30363 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____30363
                then
                  ((let uu____30369 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____30369);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____30381 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____30381))
                else ());
               (let uu____30394 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____30394))
  
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
        let fail1 uu____30468 =
          match uu____30468 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4047_30494 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4047_30494.attempting);
            wl_deferred = (uu___4047_30494.wl_deferred);
            ctr = (uu___4047_30494.ctr);
            defer_ok;
            smt_ok = (uu___4047_30494.smt_ok);
            umax_heuristic_ok = (uu___4047_30494.umax_heuristic_ok);
            tcenv = (uu___4047_30494.tcenv);
            wl_implicits = (uu___4047_30494.wl_implicits)
          }  in
        (let uu____30497 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30497
         then
           let uu____30502 = FStar_Util.string_of_bool defer_ok  in
           let uu____30504 = wl_to_string wl  in
           let uu____30506 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Common.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____30502 uu____30504 uu____30506
         else ());
        (let g1 =
           let uu____30512 = solve_and_commit env wl fail1  in
           match uu____30512 with
           | FStar_Pervasives_Native.Some
               (uu____30519::uu____30520,uu____30521) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4062_30550 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4062_30550.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4062_30550.FStar_TypeChecker_Common.univ_ineqs);
                 FStar_TypeChecker_Common.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Common.implicits
                      imps)
               }
           | uu____30551 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env
           g1.FStar_TypeChecker_Common.univ_ineqs;
         (let uu___4067_30560 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4067_30560.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4067_30560.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4067_30560.FStar_TypeChecker_Common.implicits)
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
            let uu___4079_30637 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Common.deferred =
                (uu___4079_30637.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4079_30637.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___4079_30637.FStar_TypeChecker_Common.implicits)
            }  in
          let uu____30638 =
            let uu____30640 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____30640  in
          if uu____30638
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Common.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____30652 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____30653 =
                       let uu____30655 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____30655
                        in
                     FStar_Errors.diag uu____30652 uu____30653)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____30663 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____30664 =
                        let uu____30666 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____30666
                         in
                      FStar_Errors.diag uu____30663 uu____30664)
                   else ();
                   (let uu____30672 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____30672
                      "discharge_guard'" env vc1);
                   (let uu____30674 =
                      FStar_TypeChecker_Common.check_trivial vc1  in
                    match uu____30674 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____30683 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____30684 =
                                let uu____30686 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____30686
                                 in
                              FStar_Errors.diag uu____30683 uu____30684)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____30696 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____30697 =
                                let uu____30699 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____30699
                                 in
                              FStar_Errors.diag uu____30696 uu____30697)
                           else ();
                           (let vcs =
                              let uu____30713 = FStar_Options.use_tactics ()
                                 in
                              if uu____30713
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____30735  ->
                                     (let uu____30737 =
                                        FStar_Options.set_options
                                          "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____30737);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____30781  ->
                                              match uu____30781 with
                                              | (env1,goal,opts) ->
                                                  let uu____30797 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____30797, opts)))))
                              else
                                (let uu____30800 =
                                   let uu____30807 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____30807)  in
                                 [uu____30800])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____30840  ->
                                    match uu____30840 with
                                    | (env1,goal,opts) ->
                                        let uu____30850 =
                                          FStar_TypeChecker_Common.check_trivial
                                            goal
                                           in
                                        (match uu____30850 with
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
                                                (let uu____30861 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____30862 =
                                                   let uu____30864 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____30866 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____30864 uu____30866
                                                    in
                                                 FStar_Errors.diag
                                                   uu____30861 uu____30862)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____30873 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____30874 =
                                                   let uu____30876 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____30876
                                                    in
                                                 FStar_Errors.diag
                                                   uu____30873 uu____30874)
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
      let uu____30894 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____30894 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____30903 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____30903
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____30917 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____30917 with
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
        let uu____30947 = try_teq false env t1 t2  in
        match uu____30947 with
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
            let uu____30991 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____30991 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____31004 ->
                     let uu____31017 =
                       let uu____31018 = FStar_Syntax_Subst.compress r  in
                       uu____31018.FStar_Syntax_Syntax.n  in
                     (match uu____31017 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____31023) ->
                          unresolved ctx_u'
                      | uu____31040 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____31064 = acc  in
            match uu____31064 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____31083 = hd1  in
                     (match uu____31083 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____31094 = unresolved ctx_u  in
                             if uu____31094
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____31118 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____31118
                                     then
                                       let uu____31122 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____31122
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____31131 = teq_nosmt env1 t tm
                                          in
                                       match uu____31131 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4191_31141 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4191_31141.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4191_31141.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4191_31141.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4191_31141.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4191_31141.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4191_31141.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4191_31141.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4194_31149 = hd1  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4194_31149.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4194_31149.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4194_31149.FStar_TypeChecker_Common.imp_range)
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
                                    let uu___4198_31160 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4198_31160.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4198_31160.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4198_31160.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4198_31160.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4198_31160.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4198_31160.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4198_31160.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4198_31160.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4198_31160.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4198_31160.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4198_31160.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4198_31160.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4198_31160.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4198_31160.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4198_31160.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4198_31160.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4198_31160.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4198_31160.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4198_31160.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4198_31160.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4198_31160.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4198_31160.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4198_31160.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4198_31160.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4198_31160.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4198_31160.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4198_31160.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4198_31160.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4198_31160.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4198_31160.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4198_31160.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4198_31160.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4198_31160.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4198_31160.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4198_31160.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4198_31160.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4198_31160.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4198_31160.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4198_31160.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4198_31160.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4198_31160.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4198_31160.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4198_31160.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4198_31160.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4203_31164 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4203_31164.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4203_31164.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4203_31164.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4203_31164.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4203_31164.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4203_31164.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4203_31164.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4203_31164.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4203_31164.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4203_31164.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4203_31164.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4203_31164.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4203_31164.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4203_31164.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4203_31164.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4203_31164.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4203_31164.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4203_31164.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4203_31164.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4203_31164.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4203_31164.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4203_31164.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4203_31164.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4203_31164.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4203_31164.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4203_31164.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4203_31164.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4203_31164.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4203_31164.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4203_31164.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4203_31164.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4203_31164.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4203_31164.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4203_31164.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4203_31164.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4203_31164.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4203_31164.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4203_31164.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4203_31164.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4203_31164.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4203_31164.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4203_31164.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4203_31164.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4203_31164.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____31169 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____31169
                                   then
                                     let uu____31174 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____31176 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____31178 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____31180 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____31174 uu____31176 uu____31178
                                       reason uu____31180
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4209_31187  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____31194 =
                                             let uu____31204 =
                                               let uu____31212 =
                                                 let uu____31214 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____31216 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____31218 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____31214 uu____31216
                                                   uu____31218
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____31212, r)
                                                in
                                             [uu____31204]  in
                                           FStar_Errors.add_errors
                                             uu____31194);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____31237 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____31248  ->
                                               let uu____31249 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____31251 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____31253 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____31249 uu____31251
                                                 reason uu____31253)) env2 g1
                                         true
                                        in
                                     match uu____31237 with
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
          let uu___4221_31261 = g  in
          let uu____31262 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4221_31261.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4221_31261.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4221_31261.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____31262
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
        let uu____31302 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____31302 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
          let uu____31303 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____31303
      | imp::uu____31305 ->
          let uu____31308 =
            let uu____31314 =
              let uu____31316 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____31318 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____31316 uu____31318
                imp.FStar_TypeChecker_Common.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____31314)
             in
          FStar_Errors.raise_error uu____31308
            imp.FStar_TypeChecker_Common.imp_range
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31340 = teq_nosmt env t1 t2  in
        match uu____31340 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4243_31359 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4243_31359.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred =
          (uu___4243_31359.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4243_31359.FStar_TypeChecker_Common.implicits)
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
        (let uu____31395 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31395
         then
           let uu____31400 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31402 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____31400
             uu____31402
         else ());
        (let uu____31407 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31407 with
         | (prob,x,wl) ->
             let g =
               let uu____31426 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____31435  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31426  in
             ((let uu____31454 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____31454
               then
                 let uu____31459 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____31461 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____31463 =
                   let uu____31465 = FStar_Util.must g  in
                   guard_to_string env uu____31465  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____31459 uu____31461 uu____31463
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
        let uu____31502 = check_subtyping env t1 t2  in
        match uu____31502 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31521 =
              let uu____31522 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____31522 g  in
            FStar_Pervasives_Native.Some uu____31521
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31541 = check_subtyping env t1 t2  in
        match uu____31541 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31560 =
              let uu____31561 =
                let uu____31562 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____31562]  in
              FStar_TypeChecker_Env.close_guard env uu____31561 g  in
            FStar_Pervasives_Native.Some uu____31560
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____31600 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31600
         then
           let uu____31605 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31607 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____31605
             uu____31607
         else ());
        (let uu____31612 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31612 with
         | (prob,x,wl) ->
             let g =
               let uu____31627 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____31636  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31627  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____31658 =
                      let uu____31659 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____31659]  in
                    FStar_TypeChecker_Env.close_guard env uu____31658 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31700 = subtype_nosmt env t1 t2  in
        match uu____31700 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  