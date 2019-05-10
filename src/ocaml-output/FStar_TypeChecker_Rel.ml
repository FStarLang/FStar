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
                (uu___77_569.FStar_TypeChecker_Env.nbe)
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
      ctr = (Prims.parse_int "0");
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
    uu____1887 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
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
                ctr = (wl1.ctr + (Prims.parse_int "1"));
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
           ctr = (wl.ctr + (Prims.parse_int "1"));
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
      | FStar_Syntax_Syntax.Delta_constant_at_level i when
          i > (Prims.parse_int "0") ->
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
              (if d > (Prims.parse_int "0")
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let fail1 d r t11 t21 =
            (r,
              (if d > (Prims.parse_int "0")
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
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
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
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             match r with
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  i),FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level j))
                 when
                 ((i > (Prims.parse_int "0")) || (j > (Prims.parse_int "0")))
                   && (i <> j)
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
                        aux false (n_delta + (Prims.parse_int "1")) t12 t21
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + (Prims.parse_int "1")) t11 t22
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + (Prims.parse_int "1")) t12 t22)
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
                        aux false (n_delta + (Prims.parse_int "1")) t12 t21
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + (Prims.parse_int "1")) t11 t22
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + (Prims.parse_int "1")) t12 t22)
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
          let r = aux true (Prims.parse_int "0") t1 t2  in
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
    | FStar_TypeChecker_Common.Rigid_rigid  -> (Prims.parse_int "0")
    | FStar_TypeChecker_Common.Flex_rigid_eq  -> (Prims.parse_int "1")
    | FStar_TypeChecker_Common.Flex_flex_pattern_eq  -> (Prims.parse_int "2")
    | FStar_TypeChecker_Common.Flex_rigid  -> (Prims.parse_int "3")
    | FStar_TypeChecker_Common.Rigid_flex  -> (Prims.parse_int "4")
    | FStar_TypeChecker_Common.Flex_flex  -> (Prims.parse_int "5")
  
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
                                  uu____9644 = (Prims.parse_int "0")))
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
                             uu____9673 = (Prims.parse_int "0")))
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
                                                    ((Prims.parse_int "0"),
                                                      x1)]
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
                                                    ((Prims.parse_int "0"),
                                                      x1)]
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
                                                    ((Prims.parse_int "0"),
                                                      x1)]
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
                     let uu____14920 = rhs wl1 scope env1 subst1  in
                     (match uu____14920 with
                      | (rhs_prob,wl2) ->
                          ((let uu____14941 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____14941
                            then
                              let uu____14946 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____14946
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15024 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15024 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2185_15026 = hd1  in
                       let uu____15027 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2185_15026.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2185_15026.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15027
                       }  in
                     let hd21 =
                       let uu___2188_15031 = hd2  in
                       let uu____15032 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2188_15031.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2188_15031.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15032
                       }  in
                     let uu____15035 =
                       let uu____15040 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15040
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15035 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____15061 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____15061
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15068 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____15068 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15135 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15135
                                  in
                               ((let uu____15153 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15153
                                 then
                                   let uu____15158 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15160 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15158
                                     uu____15160
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____15193 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15229 = aux wl [] env [] bs1 bs2  in
               match uu____15229 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15284 = attempt sub_probs wl2  in
                   solve env uu____15284)

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
            let uu___2223_15305 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2223_15305.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2223_15305.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15318 = try_solve env wl'  in
          match uu____15318 with
          | Success (uu____15319,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2232_15323 = wl  in
                  {
                    attempting = (uu___2232_15323.attempting);
                    wl_deferred = (uu___2232_15323.wl_deferred);
                    ctr = (uu___2232_15323.ctr);
                    defer_ok = (uu___2232_15323.defer_ok);
                    smt_ok = (uu___2232_15323.smt_ok);
                    umax_heuristic_ok = (uu___2232_15323.umax_heuristic_ok);
                    tcenv = (uu___2232_15323.tcenv);
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
        (let uu____15335 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15335 wl)

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
              let uu____15349 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15349 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15383 = lhs1  in
              match uu____15383 with
              | (uu____15386,ctx_u,uu____15388) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15396 ->
                        let uu____15397 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15397 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15446 = quasi_pattern env1 lhs1  in
              match uu____15446 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15480) ->
                  let uu____15485 = lhs1  in
                  (match uu____15485 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15500 = occurs_check ctx_u rhs1  in
                       (match uu____15500 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15551 =
                                let uu____15559 =
                                  let uu____15561 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15561
                                   in
                                FStar_Util.Inl uu____15559  in
                              (uu____15551, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15589 =
                                 let uu____15591 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15591  in
                               if uu____15589
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15618 =
                                    let uu____15626 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15626  in
                                  let uu____15632 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____15618, uu____15632)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____15676 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____15676 with
              | (rhs_hd,args) ->
                  let uu____15719 = FStar_Util.prefix args  in
                  (match uu____15719 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15791 = lhs1  in
                       (match uu____15791 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____15795 =
                              let uu____15806 =
                                let uu____15813 =
                                  let uu____15816 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____15816
                                   in
                                copy_uvar u_lhs [] uu____15813 wl1  in
                              match uu____15806 with
                              | (uu____15843,t_last_arg,wl2) ->
                                  let uu____15846 =
                                    let uu____15853 =
                                      let uu____15854 =
                                        let uu____15863 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____15863]  in
                                      FStar_List.append bs_lhs uu____15854
                                       in
                                    copy_uvar u_lhs uu____15853 t_res_lhs wl2
                                     in
                                  (match uu____15846 with
                                   | (uu____15898,lhs',wl3) ->
                                       let uu____15901 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____15901 with
                                        | (uu____15918,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____15795 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____15939 =
                                     let uu____15940 =
                                       let uu____15945 =
                                         let uu____15946 =
                                           let uu____15949 =
                                             let uu____15954 =
                                               let uu____15955 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____15955]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____15954
                                              in
                                           uu____15949
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____15946
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____15945)  in
                                     TERM uu____15940  in
                                   [uu____15939]  in
                                 let uu____15980 =
                                   let uu____15987 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____15987 with
                                   | (p1,wl3) ->
                                       let uu____16007 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____16007 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____15980 with
                                  | (sub_probs,wl3) ->
                                      let uu____16039 =
                                        let uu____16040 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____16040  in
                                      solve env1 uu____16039))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16074 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16074 with
                | (uu____16092,args) ->
                    (match args with | [] -> false | uu____16128 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16147 =
                  let uu____16148 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16148.FStar_Syntax_Syntax.n  in
                match uu____16147 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16152 -> true
                | uu____16168 -> false  in
              let uu____16170 = quasi_pattern env1 lhs1  in
              match uu____16170 with
              | FStar_Pervasives_Native.None  ->
                  let uu____16181 =
                    let uu____16183 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                      uu____16183
                     in
                  giveup_or_defer env1 orig1 wl1 uu____16181
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16192 = is_app rhs1  in
                  if uu____16192
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____16197 = is_arrow rhs1  in
                     if uu____16197
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____16202 =
                          let uu____16204 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heuristic cannot solve %s; rhs not an app or arrow"
                            uu____16204
                           in
                        giveup_or_defer env1 orig1 wl1 uu____16202))
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
                let uu____16215 = lhs  in
                (match uu____16215 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16219 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16219 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16237 =
                              let uu____16241 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16241
                               in
                            FStar_All.pipe_right uu____16237
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16262 = occurs_check ctx_uv rhs1  in
                          (match uu____16262 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16291 =
                                   let uu____16293 = FStar_Option.get msg  in
                                   Prims.op_Hat "occurs-check failed: "
                                     uu____16293
                                    in
                                 giveup_or_defer env orig wl uu____16291
                               else
                                 (let uu____16299 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____16299
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____16306 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____16306
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____16310 =
                                         let uu____16312 =
                                           names_to_string1 fvs2  in
                                         let uu____16314 =
                                           names_to_string1 fvs1  in
                                         let uu____16316 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____16312 uu____16314
                                           uu____16316
                                          in
                                       giveup_or_defer env orig wl
                                         uu____16310)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16328 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____16335 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16335 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16361 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16361
                             | (FStar_Util.Inl msg,uu____16363) ->
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
                  (let uu____16408 =
                     let uu____16425 = quasi_pattern env lhs  in
                     let uu____16432 = quasi_pattern env rhs  in
                     (uu____16425, uu____16432)  in
                   match uu____16408 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16475 = lhs  in
                       (match uu____16475 with
                        | ({ FStar_Syntax_Syntax.n = uu____16476;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____16478;_},u_lhs,uu____16480)
                            ->
                            let uu____16483 = rhs  in
                            (match uu____16483 with
                             | (uu____16484,u_rhs,uu____16486) ->
                                 let uu____16487 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16487
                                 then
                                   let uu____16494 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16494
                                 else
                                   (let uu____16497 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16497 with
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
                                        let uu____16529 =
                                          let uu____16536 =
                                            let uu____16539 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16539
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16536
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____16529 with
                                         | (uu____16551,w,wl1) ->
                                             let w_app =
                                               let uu____16557 =
                                                 let uu____16562 =
                                                   FStar_List.map
                                                     (fun uu____16573  ->
                                                        match uu____16573
                                                        with
                                                        | (z,uu____16581) ->
                                                            let uu____16586 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____16586) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____16562
                                                  in
                                               uu____16557
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16588 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16588
                                               then
                                                 let uu____16593 =
                                                   let uu____16597 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16599 =
                                                     let uu____16603 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____16605 =
                                                       let uu____16609 =
                                                         term_to_string w  in
                                                       let uu____16611 =
                                                         let uu____16615 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____16624 =
                                                           let uu____16628 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____16637 =
                                                             let uu____16641
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____16641]
                                                              in
                                                           uu____16628 ::
                                                             uu____16637
                                                            in
                                                         uu____16615 ::
                                                           uu____16624
                                                          in
                                                       uu____16609 ::
                                                         uu____16611
                                                        in
                                                     uu____16603 ::
                                                       uu____16605
                                                      in
                                                   uu____16597 :: uu____16599
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16593
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____16658 =
                                                     let uu____16663 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____16663)  in
                                                   TERM uu____16658  in
                                                 let uu____16664 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____16664
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____16672 =
                                                        let uu____16677 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____16677)
                                                         in
                                                      TERM uu____16672  in
                                                    [s1; s2])
                                                  in
                                               let uu____16678 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____16678))))))
                   | uu____16679 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____16750 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____16750
            then
              let uu____16755 = FStar_Syntax_Print.term_to_string t1  in
              let uu____16757 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____16759 = FStar_Syntax_Print.term_to_string t2  in
              let uu____16761 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____16755 uu____16757 uu____16759 uu____16761
            else ());
           (let uu____16772 = FStar_Syntax_Util.head_and_args t1  in
            match uu____16772 with
            | (head1,args1) ->
                let uu____16815 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____16815 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____16885 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____16885 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              k false (defer "universe constraints" orig wl3))
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____16911 =
                         let uu____16913 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____16915 = args_to_string args1  in
                         let uu____16919 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____16921 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____16913 uu____16915 uu____16919 uu____16921
                          in
                       giveup env1 uu____16911 orig
                     else
                       (let uu____16928 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____16933 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____16933 = FStar_Syntax_Util.Equal)
                           in
                        if uu____16928
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2481_16937 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2481_16937.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2481_16937.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2481_16937.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2481_16937.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2481_16937.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2481_16937.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2481_16937.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2481_16937.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____16947 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____16947
                                    else solve env1 wl2))
                        else
                          (let uu____16952 = base_and_refinement env1 t1  in
                           match uu____16952 with
                           | (base1,refinement1) ->
                               let uu____16977 = base_and_refinement env1 t2
                                  in
                               (match uu____16977 with
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
                                           let uu____17142 =
                                             FStar_List.fold_right
                                               (fun uu____17182  ->
                                                  fun uu____17183  ->
                                                    match (uu____17182,
                                                            uu____17183)
                                                    with
                                                    | (((a1,uu____17235),
                                                        (a2,uu____17237)),
                                                       (probs,wl3)) ->
                                                        let uu____17286 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17286
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17142 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17329 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17329
                                                 then
                                                   let uu____17334 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17334
                                                 else ());
                                                (let uu____17340 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17340
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
                                                    (let uu____17367 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17367 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17383 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17383
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17391 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17391))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____17415 =
                                                    mk_sub_probs wl3  in
                                                  match uu____17415 with
                                                  | (subprobs,wl4) ->
                                                      let wl5 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          [] wl4
                                                         in
                                                      let uu____17429 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____17429)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17455 =
                                           match uu____17455 with
                                           | (prob,reason) ->
                                               ((let uu____17466 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17466
                                                 then
                                                   let uu____17471 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____17473 =
                                                     prob_to_string env2 prob
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____17471 uu____17473
                                                     reason
                                                 else ());
                                                (let uu____17478 =
                                                   let uu____17487 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____17490 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____17487, uu____17490)
                                                    in
                                                 match uu____17478 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____17503 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____17503 with
                                                      | (head1',uu____17521)
                                                          ->
                                                          let uu____17546 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____17546
                                                           with
                                                           | (head2',uu____17564)
                                                               ->
                                                               let uu____17589
                                                                 =
                                                                 let uu____17594
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____17595
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____17594,
                                                                   uu____17595)
                                                                  in
                                                               (match uu____17589
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____17597
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17597
                                                                    then
                                                                    let uu____17602
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____17604
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____17606
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____17608
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17602
                                                                    uu____17604
                                                                    uu____17606
                                                                    uu____17608
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____17613
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2567_17621
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2567_17621.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2567_17621.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2567_17621.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2567_17621.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2567_17621.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2567_17621.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2567_17621.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2567_17621.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____17623
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17623
                                                                    then
                                                                    let uu____17628
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____17628
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____17633 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____17645 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____17645 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____17653 =
                                             let uu____17654 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____17654.FStar_Syntax_Syntax.n
                                              in
                                           match uu____17653 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____17659 -> false  in
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
                                          | uu____17662 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____17665 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2587_17701 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2587_17701.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2587_17701.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2587_17701.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2587_17701.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2587_17701.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2587_17701.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2587_17701.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2587_17701.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____17777 = destruct_flex_t scrutinee wl1  in
             match uu____17777 with
             | ((_t,uv,_args),wl2) ->
                 let uu____17788 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____17788 with
                  | (xs,pat_term,uu____17804,uu____17805) ->
                      let uu____17810 =
                        FStar_List.fold_left
                          (fun uu____17833  ->
                             fun x  ->
                               match uu____17833 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____17854 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____17854 with
                                    | (uu____17873,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____17810 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____17894 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____17894 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2627_17911 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2627_17911.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2627_17911.umax_heuristic_ok);
                                    tcenv = (uu___2627_17911.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____17923 = solve env1 wl'  in
                                (match uu____17923 with
                                 | Success (uu____17926,imps) ->
                                     let wl'1 =
                                       let uu___2635_17929 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2635_17929.wl_deferred);
                                         ctr = (uu___2635_17929.ctr);
                                         defer_ok =
                                           (uu___2635_17929.defer_ok);
                                         smt_ok = (uu___2635_17929.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2635_17929.umax_heuristic_ok);
                                         tcenv = (uu___2635_17929.tcenv);
                                         wl_implicits =
                                           (uu___2635_17929.wl_implicits)
                                       }  in
                                     let uu____17930 = solve env1 wl'1  in
                                     (match uu____17930 with
                                      | Success (uu____17933,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2643_17937 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2643_17937.attempting);
                                                 wl_deferred =
                                                   (uu___2643_17937.wl_deferred);
                                                 ctr = (uu___2643_17937.ctr);
                                                 defer_ok =
                                                   (uu___2643_17937.defer_ok);
                                                 smt_ok =
                                                   (uu___2643_17937.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2643_17937.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2643_17937.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____17938 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____17945 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____17968 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____17968
                 then
                   let uu____17973 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____17975 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____17973 uu____17975
                 else ());
                (let uu____17980 =
                   let uu____18001 =
                     let uu____18010 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18010)  in
                   let uu____18017 =
                     let uu____18026 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18026)  in
                   (uu____18001, uu____18017)  in
                 match uu____17980 with
                 | ((uu____18056,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18059;
                                   FStar_Syntax_Syntax.vars = uu____18060;_}),
                    (s,t)) ->
                     let uu____18131 =
                       let uu____18133 = is_flex scrutinee  in
                       Prims.op_Negation uu____18133  in
                     if uu____18131
                     then
                       ((let uu____18144 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18144
                         then
                           let uu____18149 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18149
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18168 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18168
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18183 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18183
                           then
                             let uu____18188 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18190 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18188 uu____18190
                           else ());
                          (let pat_discriminates uu___28_18215 =
                             match uu___28_18215 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18231;
                                  FStar_Syntax_Syntax.p = uu____18232;_},FStar_Pervasives_Native.None
                                ,uu____18233) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18247;
                                  FStar_Syntax_Syntax.p = uu____18248;_},FStar_Pervasives_Native.None
                                ,uu____18249) -> true
                             | uu____18276 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18379 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18379 with
                                       | (uu____18381,uu____18382,t') ->
                                           let uu____18400 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18400 with
                                            | (FullMatch ,uu____18412) ->
                                                true
                                            | (HeadMatch
                                               uu____18426,uu____18427) ->
                                                true
                                            | uu____18442 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18479 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18479
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18490 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18490 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18578,uu____18579) ->
                                       branches1
                                   | uu____18724 -> branches  in
                                 let uu____18779 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____18788 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____18788 with
                                        | (p,uu____18792,uu____18793) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _18822  -> FStar_Util.Inr _18822)
                                   uu____18779))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____18852 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____18852 with
                                | (p,uu____18861,e) ->
                                    ((let uu____18880 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____18880
                                      then
                                        let uu____18885 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____18887 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____18885 uu____18887
                                      else ());
                                     (let uu____18892 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _18907  -> FStar_Util.Inr _18907)
                                        uu____18892)))))
                 | ((s,t),(uu____18910,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____18913;
                                         FStar_Syntax_Syntax.vars =
                                           uu____18914;_}))
                     ->
                     let uu____18983 =
                       let uu____18985 = is_flex scrutinee  in
                       Prims.op_Negation uu____18985  in
                     if uu____18983
                     then
                       ((let uu____18996 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18996
                         then
                           let uu____19001 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19001
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19020 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19020
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19035 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19035
                           then
                             let uu____19040 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19042 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19040 uu____19042
                           else ());
                          (let pat_discriminates uu___28_19067 =
                             match uu___28_19067 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19083;
                                  FStar_Syntax_Syntax.p = uu____19084;_},FStar_Pervasives_Native.None
                                ,uu____19085) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19099;
                                  FStar_Syntax_Syntax.p = uu____19100;_},FStar_Pervasives_Native.None
                                ,uu____19101) -> true
                             | uu____19128 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19231 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19231 with
                                       | (uu____19233,uu____19234,t') ->
                                           let uu____19252 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19252 with
                                            | (FullMatch ,uu____19264) ->
                                                true
                                            | (HeadMatch
                                               uu____19278,uu____19279) ->
                                                true
                                            | uu____19294 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19331 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19331
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19342 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19342 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19430,uu____19431) ->
                                       branches1
                                   | uu____19576 -> branches  in
                                 let uu____19631 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19640 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19640 with
                                        | (p,uu____19644,uu____19645) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19674  -> FStar_Util.Inr _19674)
                                   uu____19631))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19704 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19704 with
                                | (p,uu____19713,e) ->
                                    ((let uu____19732 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19732
                                      then
                                        let uu____19737 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19739 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19737 uu____19739
                                      else ());
                                     (let uu____19744 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19759  -> FStar_Util.Inr _19759)
                                        uu____19744)))))
                 | uu____19760 ->
                     ((let uu____19782 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____19782
                       then
                         let uu____19787 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____19789 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____19787 uu____19789
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____19835 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____19835
            then
              let uu____19840 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____19842 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____19844 = FStar_Syntax_Print.term_to_string t1  in
              let uu____19846 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____19840 uu____19842 uu____19844 uu____19846
            else ());
           (let uu____19851 = head_matches_delta env1 wl1 t1 t2  in
            match uu____19851 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____19882,uu____19883) ->
                     let rec may_relate head3 =
                       let uu____19911 =
                         let uu____19912 = FStar_Syntax_Subst.compress head3
                            in
                         uu____19912.FStar_Syntax_Syntax.n  in
                       match uu____19911 with
                       | FStar_Syntax_Syntax.Tm_name uu____19916 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____19918 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____19943 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____19943 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____19945 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____19948
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____19949 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____19952,uu____19953) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____19995) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20001) ->
                           may_relate t
                       | uu____20006 -> false  in
                     let uu____20008 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20008 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20029 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20029
                          then
                            let uu____20032 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20032 with
                             | (guard,wl2) ->
                                 let uu____20039 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20039)
                          else
                            (let uu____20042 =
                               let uu____20044 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____20046 =
                                 let uu____20048 =
                                   let uu____20052 =
                                     delta_depth_of_term env1 head1  in
                                   FStar_Util.bind_opt uu____20052
                                     (fun x  ->
                                        let uu____20059 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____20059)
                                    in
                                 FStar_Util.dflt "" uu____20048  in
                               let uu____20064 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               let uu____20066 =
                                 let uu____20068 =
                                   let uu____20072 =
                                     delta_depth_of_term env1 head2  in
                                   FStar_Util.bind_opt uu____20072
                                     (fun x  ->
                                        let uu____20079 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____20079)
                                    in
                                 FStar_Util.dflt "" uu____20068  in
                               FStar_Util.format4
                                 "head mismatch (%s (%s) vs %s (%s))"
                                 uu____20044 uu____20046 uu____20064
                                 uu____20066
                                in
                             giveup env1 uu____20042 orig))
                 | (HeadMatch (true ),uu____20085) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20100 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20100 with
                        | (guard,wl2) ->
                            let uu____20107 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20107)
                     else
                       (let uu____20110 =
                          let uu____20112 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____20114 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____20112 uu____20114
                           in
                        giveup env1 uu____20110 orig)
                 | (uu____20117,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2816_20131 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2816_20131.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2816_20131.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2816_20131.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2816_20131.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2816_20131.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2816_20131.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2816_20131.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2816_20131.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20158 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20158
          then
            let uu____20161 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20161
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20167 =
                let uu____20170 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20170  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20167 t1);
             (let uu____20189 =
                let uu____20192 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20192  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20189 t2);
             (let uu____20211 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20211
              then
                let uu____20215 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20217 =
                  let uu____20219 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20221 =
                    let uu____20223 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____20223  in
                  Prims.op_Hat uu____20219 uu____20221  in
                let uu____20226 =
                  let uu____20228 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20230 =
                    let uu____20232 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____20232  in
                  Prims.op_Hat uu____20228 uu____20230  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20215 uu____20217 uu____20226
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20239,uu____20240) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20264,FStar_Syntax_Syntax.Tm_delayed uu____20265) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20289,uu____20290) ->
                  let uu____20317 =
                    let uu___2847_20318 = problem  in
                    let uu____20319 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2847_20318.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20319;
                      FStar_TypeChecker_Common.relation =
                        (uu___2847_20318.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2847_20318.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2847_20318.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2847_20318.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2847_20318.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2847_20318.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2847_20318.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2847_20318.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20317 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20320,uu____20321) ->
                  let uu____20328 =
                    let uu___2853_20329 = problem  in
                    let uu____20330 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2853_20329.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20330;
                      FStar_TypeChecker_Common.relation =
                        (uu___2853_20329.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2853_20329.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2853_20329.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2853_20329.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2853_20329.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2853_20329.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2853_20329.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2853_20329.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20328 wl
              | (uu____20331,FStar_Syntax_Syntax.Tm_ascribed uu____20332) ->
                  let uu____20359 =
                    let uu___2859_20360 = problem  in
                    let uu____20361 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2859_20360.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2859_20360.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2859_20360.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20361;
                      FStar_TypeChecker_Common.element =
                        (uu___2859_20360.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2859_20360.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2859_20360.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2859_20360.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2859_20360.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2859_20360.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20359 wl
              | (uu____20362,FStar_Syntax_Syntax.Tm_meta uu____20363) ->
                  let uu____20370 =
                    let uu___2865_20371 = problem  in
                    let uu____20372 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2865_20371.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2865_20371.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2865_20371.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20372;
                      FStar_TypeChecker_Common.element =
                        (uu___2865_20371.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2865_20371.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2865_20371.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2865_20371.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2865_20371.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2865_20371.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20370 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____20374),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____20376)) ->
                  let uu____20385 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____20385
              | (FStar_Syntax_Syntax.Tm_bvar uu____20386,uu____20387) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____20389,FStar_Syntax_Syntax.Tm_bvar uu____20390) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___29_20460 =
                    match uu___29_20460 with
                    | [] -> c
                    | bs ->
                        let uu____20488 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____20488
                     in
                  let uu____20499 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____20499 with
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
                                    let uu____20648 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____20648
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
                  let mk_t t l uu___30_20737 =
                    match uu___30_20737 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____20779 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____20779 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____20924 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____20925 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____20924
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____20925 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____20927,uu____20928) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____20959 -> true
                    | uu____20979 -> false  in
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
                      (let uu____21039 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___2967_21047 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___2967_21047.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___2967_21047.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___2967_21047.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___2967_21047.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___2967_21047.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___2967_21047.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___2967_21047.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___2967_21047.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___2967_21047.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___2967_21047.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___2967_21047.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___2967_21047.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___2967_21047.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___2967_21047.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___2967_21047.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___2967_21047.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___2967_21047.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___2967_21047.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___2967_21047.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___2967_21047.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___2967_21047.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___2967_21047.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___2967_21047.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___2967_21047.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___2967_21047.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___2967_21047.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___2967_21047.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___2967_21047.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___2967_21047.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___2967_21047.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___2967_21047.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___2967_21047.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___2967_21047.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___2967_21047.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___2967_21047.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___2967_21047.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___2967_21047.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___2967_21047.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___2967_21047.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___2967_21047.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____21039 with
                       | (uu____21052,ty,uu____21054) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21063 =
                                 let uu____21064 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21064.FStar_Syntax_Syntax.n  in
                               match uu____21063 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21067 ->
                                   let uu____21074 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21074
                               | uu____21075 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21078 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21078
                             then
                               let uu____21083 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21085 =
                                 let uu____21087 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21087
                                  in
                               let uu____21088 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21083 uu____21085 uu____21088
                             else ());
                            r1))
                     in
                  let uu____21093 =
                    let uu____21110 = maybe_eta t1  in
                    let uu____21117 = maybe_eta t2  in
                    (uu____21110, uu____21117)  in
                  (match uu____21093 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___2988_21159 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___2988_21159.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___2988_21159.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___2988_21159.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___2988_21159.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___2988_21159.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___2988_21159.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___2988_21159.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___2988_21159.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21180 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21180
                       then
                         let uu____21183 = destruct_flex_t not_abs wl  in
                         (match uu____21183 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3005_21200 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3005_21200.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3005_21200.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3005_21200.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3005_21200.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3005_21200.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3005_21200.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3005_21200.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3005_21200.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21224 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21224
                       then
                         let uu____21227 = destruct_flex_t not_abs wl  in
                         (match uu____21227 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3005_21244 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3005_21244.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3005_21244.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3005_21244.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3005_21244.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3005_21244.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3005_21244.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3005_21244.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3005_21244.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____21248 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21266,FStar_Syntax_Syntax.Tm_abs uu____21267) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21298 -> true
                    | uu____21318 -> false  in
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
                      (let uu____21378 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___2967_21386 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___2967_21386.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___2967_21386.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___2967_21386.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___2967_21386.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___2967_21386.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___2967_21386.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___2967_21386.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___2967_21386.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___2967_21386.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___2967_21386.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___2967_21386.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___2967_21386.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___2967_21386.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___2967_21386.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___2967_21386.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___2967_21386.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___2967_21386.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___2967_21386.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___2967_21386.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___2967_21386.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___2967_21386.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___2967_21386.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___2967_21386.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___2967_21386.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___2967_21386.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___2967_21386.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___2967_21386.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___2967_21386.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___2967_21386.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___2967_21386.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___2967_21386.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___2967_21386.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___2967_21386.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___2967_21386.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___2967_21386.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___2967_21386.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___2967_21386.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___2967_21386.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___2967_21386.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___2967_21386.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____21378 with
                       | (uu____21391,ty,uu____21393) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21402 =
                                 let uu____21403 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21403.FStar_Syntax_Syntax.n  in
                               match uu____21402 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21406 ->
                                   let uu____21413 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21413
                               | uu____21414 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21417 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21417
                             then
                               let uu____21422 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21424 =
                                 let uu____21426 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21426
                                  in
                               let uu____21427 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21422 uu____21424 uu____21427
                             else ());
                            r1))
                     in
                  let uu____21432 =
                    let uu____21449 = maybe_eta t1  in
                    let uu____21456 = maybe_eta t2  in
                    (uu____21449, uu____21456)  in
                  (match uu____21432 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___2988_21498 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___2988_21498.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___2988_21498.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___2988_21498.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___2988_21498.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___2988_21498.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___2988_21498.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___2988_21498.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___2988_21498.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21519 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21519
                       then
                         let uu____21522 = destruct_flex_t not_abs wl  in
                         (match uu____21522 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3005_21539 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3005_21539.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3005_21539.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3005_21539.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3005_21539.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3005_21539.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3005_21539.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3005_21539.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3005_21539.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21563 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21563
                       then
                         let uu____21566 = destruct_flex_t not_abs wl  in
                         (match uu____21566 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3005_21583 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3005_21583.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3005_21583.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3005_21583.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3005_21583.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3005_21583.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3005_21583.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3005_21583.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3005_21583.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____21587 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____21617 =
                    let uu____21622 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____21622 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3028_21650 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3028_21650.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3028_21650.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3030_21652 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3030_21652.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3030_21652.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____21653,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3028_21668 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3028_21668.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3028_21668.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3030_21670 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3030_21670.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3030_21670.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____21671 -> (x1, x2)  in
                  (match uu____21617 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____21690 = as_refinement false env t11  in
                       (match uu____21690 with
                        | (x12,phi11) ->
                            let uu____21698 = as_refinement false env t21  in
                            (match uu____21698 with
                             | (x22,phi21) ->
                                 ((let uu____21707 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21707
                                   then
                                     ((let uu____21712 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____21714 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21716 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____21712
                                         uu____21714 uu____21716);
                                      (let uu____21719 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____21721 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21723 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____21719
                                         uu____21721 uu____21723))
                                   else ());
                                  (let uu____21728 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____21728 with
                                   | (base_prob,wl1) ->
                                       let x13 =
                                         FStar_Syntax_Syntax.freshen_bv x12
                                          in
                                       let subst1 =
                                         [FStar_Syntax_Syntax.DB
                                            ((Prims.parse_int "0"), x13)]
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
                                         let uu____21799 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____21799
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____21811 =
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
                                         (let uu____21824 =
                                            let uu____21827 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____21827
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____21824
                                            (p_guard base_prob));
                                         (let uu____21846 =
                                            let uu____21849 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____21849
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____21846
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____21868 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____21868)
                                          in
                                       let has_uvars =
                                         (let uu____21873 =
                                            let uu____21875 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____21875
                                             in
                                          Prims.op_Negation uu____21873) ||
                                           (let uu____21879 =
                                              let uu____21881 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____21881
                                               in
                                            Prims.op_Negation uu____21879)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____21885 =
                                           let uu____21890 =
                                             let uu____21899 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____21899]  in
                                           mk_t_problem wl1 uu____21890 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____21885 with
                                          | (ref_prob,wl2) ->
                                              let uu____21921 =
                                                solve env1
                                                  (let uu___3072_21923 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3072_21923.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3072_21923.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3072_21923.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3072_21923.tcenv);
                                                     wl_implicits =
                                                       (uu___3072_21923.wl_implicits)
                                                   })
                                                 in
                                              (match uu____21921 with
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
                                               | Success uu____21940 ->
                                                   let guard =
                                                     let uu____21948 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____21948
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___3083_21957 =
                                                       wl3  in
                                                     {
                                                       attempting =
                                                         (uu___3083_21957.attempting);
                                                       wl_deferred =
                                                         (uu___3083_21957.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            (Prims.parse_int "1"));
                                                       defer_ok =
                                                         (uu___3083_21957.defer_ok);
                                                       smt_ok =
                                                         (uu___3083_21957.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___3083_21957.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___3083_21957.tcenv);
                                                       wl_implicits =
                                                         (uu___3083_21957.wl_implicits)
                                                     }  in
                                                   let uu____21959 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____21959))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____21962,FStar_Syntax_Syntax.Tm_uvar uu____21963) ->
                  let uu____21988 = destruct_flex_t t1 wl  in
                  (match uu____21988 with
                   | (f1,wl1) ->
                       let uu____21995 = destruct_flex_t t2 wl1  in
                       (match uu____21995 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22002;
                    FStar_Syntax_Syntax.pos = uu____22003;
                    FStar_Syntax_Syntax.vars = uu____22004;_},uu____22005),FStar_Syntax_Syntax.Tm_uvar
                 uu____22006) ->
                  let uu____22055 = destruct_flex_t t1 wl  in
                  (match uu____22055 with
                   | (f1,wl1) ->
                       let uu____22062 = destruct_flex_t t2 wl1  in
                       (match uu____22062 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22069,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22070;
                    FStar_Syntax_Syntax.pos = uu____22071;
                    FStar_Syntax_Syntax.vars = uu____22072;_},uu____22073))
                  ->
                  let uu____22122 = destruct_flex_t t1 wl  in
                  (match uu____22122 with
                   | (f1,wl1) ->
                       let uu____22129 = destruct_flex_t t2 wl1  in
                       (match uu____22129 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22136;
                    FStar_Syntax_Syntax.pos = uu____22137;
                    FStar_Syntax_Syntax.vars = uu____22138;_},uu____22139),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22140;
                    FStar_Syntax_Syntax.pos = uu____22141;
                    FStar_Syntax_Syntax.vars = uu____22142;_},uu____22143))
                  ->
                  let uu____22216 = destruct_flex_t t1 wl  in
                  (match uu____22216 with
                   | (f1,wl1) ->
                       let uu____22223 = destruct_flex_t t2 wl1  in
                       (match uu____22223 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22230,uu____22231) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22244 = destruct_flex_t t1 wl  in
                  (match uu____22244 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22251;
                    FStar_Syntax_Syntax.pos = uu____22252;
                    FStar_Syntax_Syntax.vars = uu____22253;_},uu____22254),uu____22255)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22292 = destruct_flex_t t1 wl  in
                  (match uu____22292 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22299,FStar_Syntax_Syntax.Tm_uvar uu____22300) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22313,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22314;
                    FStar_Syntax_Syntax.pos = uu____22315;
                    FStar_Syntax_Syntax.vars = uu____22316;_},uu____22317))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22354,FStar_Syntax_Syntax.Tm_arrow uu____22355) ->
                  solve_t' env
                    (let uu___3183_22383 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3183_22383.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3183_22383.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3183_22383.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3183_22383.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3183_22383.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3183_22383.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3183_22383.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3183_22383.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3183_22383.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22384;
                    FStar_Syntax_Syntax.pos = uu____22385;
                    FStar_Syntax_Syntax.vars = uu____22386;_},uu____22387),FStar_Syntax_Syntax.Tm_arrow
                 uu____22388) ->
                  solve_t' env
                    (let uu___3183_22440 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3183_22440.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3183_22440.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3183_22440.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3183_22440.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3183_22440.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3183_22440.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3183_22440.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3183_22440.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3183_22440.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22441,FStar_Syntax_Syntax.Tm_uvar uu____22442) ->
                  let uu____22455 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22455
              | (uu____22456,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22457;
                    FStar_Syntax_Syntax.pos = uu____22458;
                    FStar_Syntax_Syntax.vars = uu____22459;_},uu____22460))
                  ->
                  let uu____22497 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22497
              | (FStar_Syntax_Syntax.Tm_uvar uu____22498,uu____22499) ->
                  let uu____22512 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22512
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22513;
                    FStar_Syntax_Syntax.pos = uu____22514;
                    FStar_Syntax_Syntax.vars = uu____22515;_},uu____22516),uu____22517)
                  ->
                  let uu____22554 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22554
              | (FStar_Syntax_Syntax.Tm_refine uu____22555,uu____22556) ->
                  let t21 =
                    let uu____22564 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____22564  in
                  solve_t env
                    (let uu___3218_22590 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3218_22590.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3218_22590.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3218_22590.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3218_22590.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3218_22590.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3218_22590.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3218_22590.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3218_22590.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3218_22590.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22591,FStar_Syntax_Syntax.Tm_refine uu____22592) ->
                  let t11 =
                    let uu____22600 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22600  in
                  solve_t env
                    (let uu___3225_22626 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3225_22626.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3225_22626.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3225_22626.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3225_22626.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3225_22626.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3225_22626.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3225_22626.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3225_22626.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3225_22626.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____22708 =
                    let uu____22709 = guard_of_prob env wl problem t1 t2  in
                    match uu____22709 with
                    | (guard,wl1) ->
                        let uu____22716 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____22716
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____22935 = br1  in
                        (match uu____22935 with
                         | (p1,w1,uu____22964) ->
                             let uu____22981 = br2  in
                             (match uu____22981 with
                              | (p2,w2,uu____23004) ->
                                  let uu____23009 =
                                    let uu____23011 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23011  in
                                  if uu____23009
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23038 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23038 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23075 = br2  in
                                         (match uu____23075 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23108 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23108
                                                 in
                                              let uu____23113 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23144,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23165) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23224 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23224 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23113
                                                (fun uu____23296  ->
                                                   match uu____23296 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23333 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23333
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____23354
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____23354
                                                              then
                                                                let uu____23359
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____23361
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____23359
                                                                  uu____23361
                                                              else ());
                                                             (let uu____23367
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____23367
                                                                (fun
                                                                   uu____23403
                                                                    ->
                                                                   match uu____23403
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
                    | uu____23532 -> FStar_Pervasives_Native.None  in
                  let uu____23573 = solve_branches wl brs1 brs2  in
                  (match uu____23573 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____23624 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____23624 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____23658 =
                                FStar_List.map
                                  (fun uu____23670  ->
                                     match uu____23670 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____23658  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____23679 =
                              let uu____23680 =
                                let uu____23681 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____23681
                                  (let uu___3324_23689 = wl3  in
                                   {
                                     attempting =
                                       (uu___3324_23689.attempting);
                                     wl_deferred =
                                       (uu___3324_23689.wl_deferred);
                                     ctr = (uu___3324_23689.ctr);
                                     defer_ok = (uu___3324_23689.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3324_23689.umax_heuristic_ok);
                                     tcenv = (uu___3324_23689.tcenv);
                                     wl_implicits =
                                       (uu___3324_23689.wl_implicits)
                                   })
                                 in
                              solve env uu____23680  in
                            (match uu____23679 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____23694 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____23701,uu____23702) ->
                  let head1 =
                    let uu____23726 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23726
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23772 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23772
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23818 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23818
                    then
                      let uu____23822 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23824 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23826 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23822 uu____23824 uu____23826
                    else ());
                   (let no_free_uvars t =
                      (let uu____23840 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23840) &&
                        (let uu____23844 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23844)
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
                      let uu____23861 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23861 = FStar_Syntax_Util.Equal  in
                    let uu____23862 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23862
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23866 = equal t1 t2  in
                         (if uu____23866
                          then
                            let uu____23869 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____23869
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23874 =
                            let uu____23881 = equal t1 t2  in
                            if uu____23881
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23894 = mk_eq2 wl env orig t1 t2  in
                               match uu____23894 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____23874 with
                          | (guard,wl1) ->
                              let uu____23915 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____23915))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____23918,uu____23919) ->
                  let head1 =
                    let uu____23927 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23927
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23973 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23973
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24019 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24019
                    then
                      let uu____24023 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24025 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24027 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24023 uu____24025 uu____24027
                    else ());
                   (let no_free_uvars t =
                      (let uu____24041 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24041) &&
                        (let uu____24045 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24045)
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
                      let uu____24062 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24062 = FStar_Syntax_Util.Equal  in
                    let uu____24063 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24063
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24067 = equal t1 t2  in
                         (if uu____24067
                          then
                            let uu____24070 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24070
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24075 =
                            let uu____24082 = equal t1 t2  in
                            if uu____24082
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24095 = mk_eq2 wl env orig t1 t2  in
                               match uu____24095 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24075 with
                          | (guard,wl1) ->
                              let uu____24116 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24116))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24119,uu____24120) ->
                  let head1 =
                    let uu____24122 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24122
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24168 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24168
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24214 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24214
                    then
                      let uu____24218 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24220 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24222 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24218 uu____24220 uu____24222
                    else ());
                   (let no_free_uvars t =
                      (let uu____24236 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24236) &&
                        (let uu____24240 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24240)
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
                      let uu____24257 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24257 = FStar_Syntax_Util.Equal  in
                    let uu____24258 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24258
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24262 = equal t1 t2  in
                         (if uu____24262
                          then
                            let uu____24265 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24265
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24270 =
                            let uu____24277 = equal t1 t2  in
                            if uu____24277
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24290 = mk_eq2 wl env orig t1 t2  in
                               match uu____24290 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24270 with
                          | (guard,wl1) ->
                              let uu____24311 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24311))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24314,uu____24315) ->
                  let head1 =
                    let uu____24317 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24317
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24363 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24363
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24409 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24409
                    then
                      let uu____24413 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24415 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24417 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24413 uu____24415 uu____24417
                    else ());
                   (let no_free_uvars t =
                      (let uu____24431 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24431) &&
                        (let uu____24435 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24435)
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
                      let uu____24452 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24452 = FStar_Syntax_Util.Equal  in
                    let uu____24453 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24453
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24457 = equal t1 t2  in
                         (if uu____24457
                          then
                            let uu____24460 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24460
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24465 =
                            let uu____24472 = equal t1 t2  in
                            if uu____24472
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24485 = mk_eq2 wl env orig t1 t2  in
                               match uu____24485 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24465 with
                          | (guard,wl1) ->
                              let uu____24506 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24506))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____24509,uu____24510) ->
                  let head1 =
                    let uu____24512 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24512
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24558 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24558
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24604 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24604
                    then
                      let uu____24608 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24610 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24612 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24608 uu____24610 uu____24612
                    else ());
                   (let no_free_uvars t =
                      (let uu____24626 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24626) &&
                        (let uu____24630 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24630)
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
                      let uu____24647 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24647 = FStar_Syntax_Util.Equal  in
                    let uu____24648 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24648
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24652 = equal t1 t2  in
                         (if uu____24652
                          then
                            let uu____24655 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24655
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24660 =
                            let uu____24667 = equal t1 t2  in
                            if uu____24667
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24680 = mk_eq2 wl env orig t1 t2  in
                               match uu____24680 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24660 with
                          | (guard,wl1) ->
                              let uu____24701 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24701))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____24704,uu____24705) ->
                  let head1 =
                    let uu____24723 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24723
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24769 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24769
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24815 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24815
                    then
                      let uu____24819 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24821 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24823 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24819 uu____24821 uu____24823
                    else ());
                   (let no_free_uvars t =
                      (let uu____24837 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24837) &&
                        (let uu____24841 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24841)
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
                      let uu____24858 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24858 = FStar_Syntax_Util.Equal  in
                    let uu____24859 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24859
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24863 = equal t1 t2  in
                         (if uu____24863
                          then
                            let uu____24866 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24866
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24871 =
                            let uu____24878 = equal t1 t2  in
                            if uu____24878
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24891 = mk_eq2 wl env orig t1 t2  in
                               match uu____24891 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24871 with
                          | (guard,wl1) ->
                              let uu____24912 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24912))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24915,FStar_Syntax_Syntax.Tm_match uu____24916) ->
                  let head1 =
                    let uu____24940 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24940
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24986 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24986
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25032 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25032
                    then
                      let uu____25036 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25038 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25040 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25036 uu____25038 uu____25040
                    else ());
                   (let no_free_uvars t =
                      (let uu____25054 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25054) &&
                        (let uu____25058 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25058)
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
                      let uu____25075 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25075 = FStar_Syntax_Util.Equal  in
                    let uu____25076 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25076
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25080 = equal t1 t2  in
                         (if uu____25080
                          then
                            let uu____25083 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25083
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25088 =
                            let uu____25095 = equal t1 t2  in
                            if uu____25095
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25108 = mk_eq2 wl env orig t1 t2  in
                               match uu____25108 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25088 with
                          | (guard,wl1) ->
                              let uu____25129 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25129))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25132,FStar_Syntax_Syntax.Tm_uinst uu____25133) ->
                  let head1 =
                    let uu____25141 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25141
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25181 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25181
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25221 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25221
                    then
                      let uu____25225 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25227 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25229 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25225 uu____25227 uu____25229
                    else ());
                   (let no_free_uvars t =
                      (let uu____25243 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25243) &&
                        (let uu____25247 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25247)
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
                      let uu____25264 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25264 = FStar_Syntax_Util.Equal  in
                    let uu____25265 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25265
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25269 = equal t1 t2  in
                         (if uu____25269
                          then
                            let uu____25272 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25272
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25277 =
                            let uu____25284 = equal t1 t2  in
                            if uu____25284
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25297 = mk_eq2 wl env orig t1 t2  in
                               match uu____25297 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25277 with
                          | (guard,wl1) ->
                              let uu____25318 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25318))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25321,FStar_Syntax_Syntax.Tm_name uu____25322) ->
                  let head1 =
                    let uu____25324 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25324
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25364 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25364
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25404 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25404
                    then
                      let uu____25408 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25410 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25412 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25408 uu____25410 uu____25412
                    else ());
                   (let no_free_uvars t =
                      (let uu____25426 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25426) &&
                        (let uu____25430 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25430)
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
                      let uu____25447 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25447 = FStar_Syntax_Util.Equal  in
                    let uu____25448 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25448
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25452 = equal t1 t2  in
                         (if uu____25452
                          then
                            let uu____25455 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25455
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25460 =
                            let uu____25467 = equal t1 t2  in
                            if uu____25467
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25480 = mk_eq2 wl env orig t1 t2  in
                               match uu____25480 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25460 with
                          | (guard,wl1) ->
                              let uu____25501 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25501))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25504,FStar_Syntax_Syntax.Tm_constant uu____25505) ->
                  let head1 =
                    let uu____25507 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25507
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25547 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25547
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25587 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25587
                    then
                      let uu____25591 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25593 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25595 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25591 uu____25593 uu____25595
                    else ());
                   (let no_free_uvars t =
                      (let uu____25609 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25609) &&
                        (let uu____25613 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25613)
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
                      let uu____25630 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25630 = FStar_Syntax_Util.Equal  in
                    let uu____25631 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25631
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25635 = equal t1 t2  in
                         (if uu____25635
                          then
                            let uu____25638 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25638
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25643 =
                            let uu____25650 = equal t1 t2  in
                            if uu____25650
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25663 = mk_eq2 wl env orig t1 t2  in
                               match uu____25663 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25643 with
                          | (guard,wl1) ->
                              let uu____25684 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25684))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25687,FStar_Syntax_Syntax.Tm_fvar uu____25688) ->
                  let head1 =
                    let uu____25690 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25690
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25730 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25730
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25770 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25770
                    then
                      let uu____25774 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25776 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25778 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25774 uu____25776 uu____25778
                    else ());
                   (let no_free_uvars t =
                      (let uu____25792 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25792) &&
                        (let uu____25796 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25796)
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
                      let uu____25813 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25813 = FStar_Syntax_Util.Equal  in
                    let uu____25814 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25814
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25818 = equal t1 t2  in
                         (if uu____25818
                          then
                            let uu____25821 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25821
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25826 =
                            let uu____25833 = equal t1 t2  in
                            if uu____25833
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25846 = mk_eq2 wl env orig t1 t2  in
                               match uu____25846 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25826 with
                          | (guard,wl1) ->
                              let uu____25867 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25867))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25870,FStar_Syntax_Syntax.Tm_app uu____25871) ->
                  let head1 =
                    let uu____25889 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25889
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25929 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25929
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25969 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25969
                    then
                      let uu____25973 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25975 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25977 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25973 uu____25975 uu____25977
                    else ());
                   (let no_free_uvars t =
                      (let uu____25991 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25991) &&
                        (let uu____25995 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25995)
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
                      let uu____26012 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26012 = FStar_Syntax_Util.Equal  in
                    let uu____26013 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26013
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26017 = equal t1 t2  in
                         (if uu____26017
                          then
                            let uu____26020 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26020
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26025 =
                            let uu____26032 = equal t1 t2  in
                            if uu____26032
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26045 = mk_eq2 wl env orig t1 t2  in
                               match uu____26045 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26025 with
                          | (guard,wl1) ->
                              let uu____26066 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26066))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26069,FStar_Syntax_Syntax.Tm_let uu____26070) ->
                  let uu____26097 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26097
                  then
                    let uu____26100 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26100
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____26104,uu____26105) ->
                  let uu____26119 =
                    let uu____26125 =
                      let uu____26127 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26129 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26131 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26133 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26127 uu____26129 uu____26131 uu____26133
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26125)
                     in
                  FStar_Errors.raise_error uu____26119
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26137,FStar_Syntax_Syntax.Tm_let uu____26138) ->
                  let uu____26152 =
                    let uu____26158 =
                      let uu____26160 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26162 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26164 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26166 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26160 uu____26162 uu____26164 uu____26166
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26158)
                     in
                  FStar_Errors.raise_error uu____26152
                    t1.FStar_Syntax_Syntax.pos
              | uu____26170 -> giveup env "head tag mismatch" orig))))

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
          (let uu____26234 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26234
           then
             let uu____26239 =
               let uu____26241 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26241  in
             let uu____26242 =
               let uu____26244 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26244  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26239 uu____26242
           else ());
          (let uu____26248 =
             let uu____26250 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26250  in
           if uu____26248
           then
             let uu____26253 =
               let uu____26255 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____26257 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____26255 uu____26257
                in
             giveup env uu____26253 orig
           else
             (let uu____26262 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____26262 with
              | (ret_sub_prob,wl1) ->
                  let uu____26270 =
                    FStar_List.fold_right2
                      (fun uu____26307  ->
                         fun uu____26308  ->
                           fun uu____26309  ->
                             match (uu____26307, uu____26308, uu____26309)
                             with
                             | ((a1,uu____26353),(a2,uu____26355),(arg_sub_probs,wl2))
                                 ->
                                 let uu____26388 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____26388 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____26270 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____26418 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____26418  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____26426 = attempt sub_probs wl3  in
                       solve env uu____26426)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____26449 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____26452)::[] -> wp1
              | uu____26477 ->
                  let uu____26488 =
                    let uu____26490 =
                      let uu____26492 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____26492  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____26490
                     in
                  failwith uu____26488
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____26499 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____26499]
              | x -> x  in
            let uu____26501 =
              let uu____26512 =
                let uu____26521 =
                  let uu____26522 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____26522 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____26521  in
              [uu____26512]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____26501;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____26540 = lift_c1 ()  in solve_eq uu____26540 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___31_26549  ->
                       match uu___31_26549 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____26554 -> false))
                in
             let uu____26556 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____26586)::uu____26587,(wp2,uu____26589)::uu____26590)
                   -> (wp1, wp2)
               | uu____26663 ->
                   let uu____26688 =
                     let uu____26694 =
                       let uu____26696 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____26698 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____26696 uu____26698
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____26694)
                      in
                   FStar_Errors.raise_error uu____26688
                     env.FStar_TypeChecker_Env.range
                in
             match uu____26556 with
             | (wpc1,wpc2) ->
                 let uu____26708 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____26708
                 then
                   let uu____26713 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____26713 wl
                 else
                   (let uu____26717 =
                      let uu____26724 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____26724  in
                    match uu____26717 with
                    | (c2_decl,qualifiers) ->
                        let uu____26745 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____26745
                        then
                          let c1_repr =
                            let uu____26752 =
                              let uu____26753 =
                                let uu____26754 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____26754  in
                              let uu____26755 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____26753 uu____26755
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____26752
                             in
                          let c2_repr =
                            let uu____26757 =
                              let uu____26758 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____26759 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____26758 uu____26759
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____26757
                             in
                          let uu____26760 =
                            let uu____26765 =
                              let uu____26767 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____26769 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____26767 uu____26769
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____26765
                             in
                          (match uu____26760 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____26775 = attempt [prob] wl2  in
                               solve env uu____26775)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____26790 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____26790
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____26799 =
                                     let uu____26806 =
                                       let uu____26807 =
                                         let uu____26824 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____26827 =
                                           let uu____26838 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____26847 =
                                             let uu____26858 =
                                               let uu____26867 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____26867
                                                in
                                             [uu____26858]  in
                                           uu____26838 :: uu____26847  in
                                         (uu____26824, uu____26827)  in
                                       FStar_Syntax_Syntax.Tm_app uu____26807
                                        in
                                     FStar_Syntax_Syntax.mk uu____26806  in
                                   uu____26799 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____26916 =
                                    let uu____26923 =
                                      let uu____26924 =
                                        let uu____26941 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____26944 =
                                          let uu____26955 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____26964 =
                                            let uu____26975 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____26984 =
                                              let uu____26995 =
                                                let uu____27004 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____27004
                                                 in
                                              [uu____26995]  in
                                            uu____26975 :: uu____26984  in
                                          uu____26955 :: uu____26964  in
                                        (uu____26941, uu____26944)  in
                                      FStar_Syntax_Syntax.Tm_app uu____26924
                                       in
                                    FStar_Syntax_Syntax.mk uu____26923  in
                                  uu____26916 FStar_Pervasives_Native.None r)
                              in
                           (let uu____27058 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____27058
                            then
                              let uu____27063 =
                                let uu____27065 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____27065
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____27063
                            else ());
                           (let uu____27069 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____27069 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____27078 =
                                    let uu____27081 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _27084  ->
                                         FStar_Pervasives_Native.Some _27084)
                                      uu____27081
                                     in
                                  solve_prob orig uu____27078 [] wl1  in
                                let uu____27085 = attempt [base_prob] wl2  in
                                solve env uu____27085))))
           in
        let uu____27086 = FStar_Util.physical_equality c1 c2  in
        if uu____27086
        then
          let uu____27089 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____27089
        else
          ((let uu____27093 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____27093
            then
              let uu____27098 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____27100 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____27098
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____27100
            else ());
           (let uu____27105 =
              let uu____27114 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____27117 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____27114, uu____27117)  in
            match uu____27105 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____27135),FStar_Syntax_Syntax.Total
                    (t2,uu____27137)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____27154 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____27154 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____27156,FStar_Syntax_Syntax.Total uu____27157) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____27176),FStar_Syntax_Syntax.Total
                    (t2,uu____27178)) ->
                     let uu____27195 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____27195 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____27198),FStar_Syntax_Syntax.GTotal
                    (t2,uu____27200)) ->
                     let uu____27217 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____27217 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____27220),FStar_Syntax_Syntax.GTotal
                    (t2,uu____27222)) ->
                     let uu____27239 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____27239 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____27241,FStar_Syntax_Syntax.Comp uu____27242) ->
                     let uu____27251 =
                       let uu___3573_27254 = problem  in
                       let uu____27257 =
                         let uu____27258 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27258
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3573_27254.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____27257;
                         FStar_TypeChecker_Common.relation =
                           (uu___3573_27254.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3573_27254.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3573_27254.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3573_27254.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3573_27254.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3573_27254.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3573_27254.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3573_27254.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____27251 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____27259,FStar_Syntax_Syntax.Comp uu____27260) ->
                     let uu____27269 =
                       let uu___3573_27272 = problem  in
                       let uu____27275 =
                         let uu____27276 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27276
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3573_27272.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____27275;
                         FStar_TypeChecker_Common.relation =
                           (uu___3573_27272.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3573_27272.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3573_27272.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3573_27272.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3573_27272.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3573_27272.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3573_27272.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3573_27272.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____27269 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____27277,FStar_Syntax_Syntax.GTotal uu____27278) ->
                     let uu____27287 =
                       let uu___3585_27290 = problem  in
                       let uu____27293 =
                         let uu____27294 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27294
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3585_27290.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3585_27290.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3585_27290.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____27293;
                         FStar_TypeChecker_Common.element =
                           (uu___3585_27290.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3585_27290.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3585_27290.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3585_27290.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3585_27290.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3585_27290.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____27287 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____27295,FStar_Syntax_Syntax.Total uu____27296) ->
                     let uu____27305 =
                       let uu___3585_27308 = problem  in
                       let uu____27311 =
                         let uu____27312 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27312
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3585_27308.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3585_27308.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3585_27308.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____27311;
                         FStar_TypeChecker_Common.element =
                           (uu___3585_27308.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3585_27308.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3585_27308.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3585_27308.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3585_27308.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3585_27308.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____27305 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____27313,FStar_Syntax_Syntax.Comp uu____27314) ->
                     let uu____27315 =
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
                     if uu____27315
                     then
                       let uu____27318 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____27318 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____27325 =
                            let uu____27330 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____27330
                            then (c1_comp, c2_comp)
                            else
                              (let uu____27339 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____27340 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____27339, uu____27340))
                             in
                          match uu____27325 with
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
                           (let uu____27348 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____27348
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____27356 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____27356 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____27359 =
                                  let uu____27361 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____27363 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____27361 uu____27363
                                   in
                                giveup env uu____27359 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____27374 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____27374 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____27424 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____27424 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____27449 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____27480  ->
                match uu____27480 with
                | (u1,u2) ->
                    let uu____27488 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____27490 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____27488 uu____27490))
         in
      FStar_All.pipe_right uu____27449 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____27527,[])) when
          let uu____27554 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____27554 -> "{}"
      | uu____27557 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____27584 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____27584
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____27596 =
              FStar_List.map
                (fun uu____27609  ->
                   match uu____27609 with
                   | (uu____27616,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____27596 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____27627 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____27627 imps
  
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
                  let uu____27684 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____27684
                  then
                    let uu____27692 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____27694 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____27692
                      (rel_to_string rel) uu____27694
                  else "TOP"  in
                let uu____27700 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____27700 with
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
              let uu____27760 =
                let uu____27763 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _27766  -> FStar_Pervasives_Native.Some _27766)
                  uu____27763
                 in
              FStar_Syntax_Syntax.new_bv uu____27760 t1  in
            let uu____27767 =
              let uu____27772 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____27772
               in
            match uu____27767 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____27832 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____27832
         then
           let uu____27837 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____27837
         else ());
        (let uu____27844 =
           FStar_Util.record_time (fun uu____27851  -> solve env probs)  in
         match uu____27844 with
         | (sol,ms) ->
             ((let uu____27863 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____27863
               then
                 let uu____27868 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____27868
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____27881 =
                     FStar_Util.record_time
                       (fun uu____27888  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____27881 with
                    | ((),ms1) ->
                        ((let uu____27899 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____27899
                          then
                            let uu____27904 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____27904
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____27918 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____27918
                     then
                       let uu____27925 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____27925
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
          ((let uu____27952 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____27952
            then
              let uu____27957 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____27957
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____27964 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____27964
             then
               let uu____27969 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____27969
             else ());
            (let f2 =
               let uu____27975 =
                 let uu____27976 = FStar_Syntax_Util.unmeta f1  in
                 uu____27976.FStar_Syntax_Syntax.n  in
               match uu____27975 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____27980 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3701_27981 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___3701_27981.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___3701_27981.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___3701_27981.FStar_TypeChecker_Env.implicits)
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
            let uu____28036 =
              let uu____28037 =
                let uu____28038 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _28039  ->
                       FStar_TypeChecker_Common.NonTrivial _28039)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____28038;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____28037  in
            FStar_All.pipe_left
              (fun _28046  -> FStar_Pervasives_Native.Some _28046)
              uu____28036
  
let with_guard_no_simp :
  'Auu____28056 .
    'Auu____28056 ->
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
            let uu____28079 =
              let uu____28080 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _28081  -> FStar_TypeChecker_Common.NonTrivial _28081)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____28080;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____28079
  
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
          (let uu____28114 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____28114
           then
             let uu____28119 = FStar_Syntax_Print.term_to_string t1  in
             let uu____28121 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____28119
               uu____28121
           else ());
          (let uu____28126 =
             let uu____28131 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____28131
              in
           match uu____28126 with
           | (prob,wl) ->
               let g =
                 let uu____28139 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____28149  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____28139  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____28185 = try_teq true env t1 t2  in
        match uu____28185 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____28190 = FStar_TypeChecker_Env.get_range env  in
              let uu____28191 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____28190 uu____28191);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____28199 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____28199
              then
                let uu____28204 = FStar_Syntax_Print.term_to_string t1  in
                let uu____28206 = FStar_Syntax_Print.term_to_string t2  in
                let uu____28208 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____28204
                  uu____28206 uu____28208
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
          let uu____28234 = FStar_TypeChecker_Env.get_range env  in
          let uu____28235 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____28234 uu____28235
  
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
        (let uu____28264 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____28264
         then
           let uu____28269 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____28271 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____28269 uu____28271
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____28282 =
           let uu____28289 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____28289 "sub_comp"
            in
         match uu____28282 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____28302 =
                 FStar_Util.record_time
                   (fun uu____28314  ->
                      let uu____28315 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____28326  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____28315)
                  in
               match uu____28302 with
               | (r,ms) ->
                   ((let uu____28357 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____28357
                     then
                       let uu____28362 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____28364 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____28366 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____28362 uu____28364
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____28366
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
      fun uu____28404  ->
        match uu____28404 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____28447 =
                 let uu____28453 =
                   let uu____28455 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____28457 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____28455 uu____28457
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____28453)  in
               let uu____28461 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____28447 uu____28461)
               in
            let equiv1 v1 v' =
              let uu____28474 =
                let uu____28479 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____28480 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____28479, uu____28480)  in
              match uu____28474 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____28500 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____28531 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____28531 with
                      | FStar_Syntax_Syntax.U_unif uu____28538 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____28567  ->
                                    match uu____28567 with
                                    | (u,v') ->
                                        let uu____28576 = equiv1 v1 v'  in
                                        if uu____28576
                                        then
                                          let uu____28581 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____28581 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____28602 -> []))
               in
            let uu____28607 =
              let wl =
                let uu___3792_28611 = empty_worklist env  in
                {
                  attempting = (uu___3792_28611.attempting);
                  wl_deferred = (uu___3792_28611.wl_deferred);
                  ctr = (uu___3792_28611.ctr);
                  defer_ok = false;
                  smt_ok = (uu___3792_28611.smt_ok);
                  umax_heuristic_ok = (uu___3792_28611.umax_heuristic_ok);
                  tcenv = (uu___3792_28611.tcenv);
                  wl_implicits = (uu___3792_28611.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____28630  ->
                      match uu____28630 with
                      | (lb,v1) ->
                          let uu____28637 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____28637 with
                           | USolved wl1 -> ()
                           | uu____28640 -> fail1 lb v1)))
               in
            let rec check_ineq uu____28651 =
              match uu____28651 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____28663) -> true
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
                      uu____28687,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____28689,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____28700) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____28708,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____28717 -> false)
               in
            let uu____28723 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____28740  ->
                      match uu____28740 with
                      | (u,v1) ->
                          let uu____28748 = check_ineq (u, v1)  in
                          if uu____28748
                          then true
                          else
                            ((let uu____28756 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____28756
                              then
                                let uu____28761 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____28763 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____28761
                                  uu____28763
                              else ());
                             false)))
               in
            if uu____28723
            then ()
            else
              ((let uu____28773 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____28773
                then
                  ((let uu____28779 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____28779);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____28791 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____28791))
                else ());
               (let uu____28804 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____28804))
  
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
        let fail1 uu____28878 =
          match uu____28878 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___3869_28904 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___3869_28904.attempting);
            wl_deferred = (uu___3869_28904.wl_deferred);
            ctr = (uu___3869_28904.ctr);
            defer_ok;
            smt_ok = (uu___3869_28904.smt_ok);
            umax_heuristic_ok = (uu___3869_28904.umax_heuristic_ok);
            tcenv = (uu___3869_28904.tcenv);
            wl_implicits = (uu___3869_28904.wl_implicits)
          }  in
        (let uu____28907 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____28907
         then
           let uu____28912 = FStar_Util.string_of_bool defer_ok  in
           let uu____28914 = wl_to_string wl  in
           let uu____28916 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____28912 uu____28914 uu____28916
         else ());
        (let g1 =
           let uu____28922 = solve_and_commit env wl fail1  in
           match uu____28922 with
           | FStar_Pervasives_Native.Some
               (uu____28929::uu____28930,uu____28931) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___3884_28960 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___3884_28960.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___3884_28960.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____28961 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___3889_28970 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___3889_28970.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___3889_28970.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___3889_28970.FStar_TypeChecker_Env.implicits)
          }))
  
let (solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints false env g 
let (solve_some_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints true env g 
let (last_proof_ns :
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (maybe_update_proof_ns : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns  in
    let uu____29013 = FStar_ST.op_Bang last_proof_ns  in
    match uu____29013 with
    | FStar_Pervasives_Native.None  ->
        FStar_ST.op_Colon_Equals last_proof_ns
          (FStar_Pervasives_Native.Some pns)
    | FStar_Pervasives_Native.Some old ->
        if old = pns
        then ()
        else
          ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
             ();
           FStar_ST.op_Colon_Equals last_proof_ns
             (FStar_Pervasives_Native.Some pns))
  
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
            let uu___3908_29138 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___3908_29138.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___3908_29138.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___3908_29138.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____29139 =
            let uu____29141 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____29141  in
          if uu____29139
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____29153 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____29154 =
                       let uu____29156 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____29156
                        in
                     FStar_Errors.diag uu____29153 uu____29154)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____29164 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____29165 =
                        let uu____29167 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____29167
                         in
                      FStar_Errors.diag uu____29164 uu____29165)
                   else ();
                   (let uu____29173 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____29173
                      "discharge_guard'" env vc1);
                   (let uu____29175 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____29175 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____29184 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____29185 =
                                let uu____29187 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____29187
                                 in
                              FStar_Errors.diag uu____29184 uu____29185)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____29197 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____29198 =
                                let uu____29200 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____29200
                                 in
                              FStar_Errors.diag uu____29197 uu____29198)
                           else ();
                           (let vcs =
                              let uu____29214 = FStar_Options.use_tactics ()
                                 in
                              if uu____29214
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____29236  ->
                                     (let uu____29238 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____29238);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____29282  ->
                                              match uu____29282 with
                                              | (env1,goal,opts) ->
                                                  let uu____29298 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____29298, opts)))))
                              else
                                (let uu____29301 =
                                   let uu____29308 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____29308)  in
                                 [uu____29301])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____29341  ->
                                    match uu____29341 with
                                    | (env1,goal,opts) ->
                                        let uu____29351 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____29351 with
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
                                              maybe_update_proof_ns env1;
                                              if debug1
                                              then
                                                (let uu____29363 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____29364 =
                                                   let uu____29366 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____29368 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____29366 uu____29368
                                                    in
                                                 FStar_Errors.diag
                                                   uu____29363 uu____29364)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____29375 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____29376 =
                                                   let uu____29378 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____29378
                                                    in
                                                 FStar_Errors.diag
                                                   uu____29375 uu____29376)
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
      let uu____29396 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____29396 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____29405 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____29405
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____29419 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____29419 with
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
        let uu____29449 = try_teq false env t1 t2  in
        match uu____29449 with
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
            let uu____29493 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____29493 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____29506 ->
                     let uu____29519 =
                       let uu____29520 = FStar_Syntax_Subst.compress r  in
                       uu____29520.FStar_Syntax_Syntax.n  in
                     (match uu____29519 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____29525) ->
                          unresolved ctx_u'
                      | uu____29542 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____29566 = acc  in
            match uu____29566 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____29585 = hd1  in
                     (match uu____29585 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____29596 = unresolved ctx_u  in
                             if uu____29596
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____29620 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____29620
                                     then
                                       let uu____29624 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____29624
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____29633 = teq_nosmt env1 t tm
                                          in
                                       match uu____29633 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Env.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4021_29643 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4021_29643.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4021_29643.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4021_29643.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4021_29643.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4021_29643.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4021_29643.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4021_29643.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4024_29651 = hd1  in
                                       {
                                         FStar_TypeChecker_Env.imp_reason =
                                           (uu___4024_29651.FStar_TypeChecker_Env.imp_reason);
                                         FStar_TypeChecker_Env.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Env.imp_tm =
                                           (uu___4024_29651.FStar_TypeChecker_Env.imp_tm);
                                         FStar_TypeChecker_Env.imp_range =
                                           (uu___4024_29651.FStar_TypeChecker_Env.imp_range)
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
                                    let uu___4028_29662 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4028_29662.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4028_29662.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4028_29662.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4028_29662.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4028_29662.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4028_29662.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4028_29662.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4028_29662.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4028_29662.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___4028_29662.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4028_29662.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4028_29662.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4028_29662.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4028_29662.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4028_29662.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4028_29662.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4028_29662.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4028_29662.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4028_29662.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4028_29662.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4028_29662.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4028_29662.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4028_29662.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4028_29662.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4028_29662.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4028_29662.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4028_29662.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4028_29662.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4028_29662.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4028_29662.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4028_29662.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4028_29662.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4028_29662.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4028_29662.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4028_29662.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4028_29662.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4028_29662.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4028_29662.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4028_29662.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4028_29662.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4028_29662.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4028_29662.FStar_TypeChecker_Env.nbe)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4033_29666 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4033_29666.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4033_29666.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4033_29666.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4033_29666.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4033_29666.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4033_29666.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4033_29666.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4033_29666.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4033_29666.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4033_29666.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___4033_29666.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4033_29666.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4033_29666.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4033_29666.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4033_29666.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4033_29666.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4033_29666.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4033_29666.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4033_29666.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4033_29666.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4033_29666.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4033_29666.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4033_29666.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4033_29666.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4033_29666.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4033_29666.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4033_29666.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4033_29666.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4033_29666.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4033_29666.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4033_29666.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4033_29666.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4033_29666.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4033_29666.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4033_29666.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4033_29666.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4033_29666.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4033_29666.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4033_29666.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4033_29666.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4033_29666.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4033_29666.FStar_TypeChecker_Env.nbe)
                                      }
                                    else env1  in
                                  (let uu____29671 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____29671
                                   then
                                     let uu____29676 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____29678 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____29680 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____29682 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____29676 uu____29678 uu____29680
                                       reason uu____29682
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4039_29689  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____29696 =
                                             let uu____29706 =
                                               let uu____29714 =
                                                 let uu____29716 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____29718 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____29720 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____29716 uu____29718
                                                   uu____29720
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____29714, r)
                                                in
                                             [uu____29706]  in
                                           FStar_Errors.add_errors
                                             uu____29696);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___4047_29740 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___4047_29740.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___4047_29740.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___4047_29740.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____29744 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____29755  ->
                                               let uu____29756 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____29758 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____29760 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____29756 uu____29758
                                                 reason uu____29760)) env2 g2
                                         true
                                        in
                                     match uu____29744 with
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
          let uu___4055_29768 = g  in
          let uu____29769 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4055_29768.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4055_29768.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___4055_29768.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____29769
          }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun env  -> fun g  -> resolve_implicits' env true false g 
let (resolve_implicits_tac :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun env  -> fun g  -> resolve_implicits' env false true g 
let (force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> unit) =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____29812 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____29812 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____29813 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____29813
      | imp::uu____29815 ->
          let uu____29818 =
            let uu____29824 =
              let uu____29826 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____29828 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____29826 uu____29828 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____29824)
             in
          FStar_Errors.raise_error uu____29818
            imp.FStar_TypeChecker_Env.imp_range
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____29850 = teq_nosmt env t1 t2  in
        match uu____29850 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4077_29869 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___4077_29869.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___4077_29869.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___4077_29869.FStar_TypeChecker_Env.implicits)
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
        (let uu____29905 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____29905
         then
           let uu____29910 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____29912 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____29910
             uu____29912
         else ());
        (let uu____29917 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____29917 with
         | (prob,x,wl) ->
             let g =
               let uu____29936 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____29947  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____29936  in
             ((let uu____29968 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____29968
               then
                 let uu____29973 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____29975 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____29977 =
                   let uu____29979 = FStar_Util.must g  in
                   guard_to_string env uu____29979  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____29973 uu____29975 uu____29977
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
        let uu____30016 = check_subtyping env t1 t2  in
        match uu____30016 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____30035 =
              let uu____30036 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____30036 g  in
            FStar_Pervasives_Native.Some uu____30035
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____30055 = check_subtyping env t1 t2  in
        match uu____30055 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____30074 =
              let uu____30075 =
                let uu____30076 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____30076]  in
              FStar_TypeChecker_Env.close_guard env uu____30075 g  in
            FStar_Pervasives_Native.Some uu____30074
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____30114 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30114
         then
           let uu____30119 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____30121 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____30119
             uu____30121
         else ());
        (let uu____30126 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____30126 with
         | (prob,x,wl) ->
             let g =
               let uu____30141 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____30152  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30141  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____30176 =
                      let uu____30177 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____30177]  in
                    FStar_TypeChecker_Env.close_guard env uu____30176 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____30218 = subtype_nosmt env t1 t2  in
        match uu____30218 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  