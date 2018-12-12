open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____39 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____75 -> false
  
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
                    let uu____499 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____499;
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
                     (let uu___354_531 = wl  in
                      {
                        attempting = (uu___354_531.attempting);
                        wl_deferred = (uu___354_531.wl_deferred);
                        ctr = (uu___354_531.ctr);
                        defer_ok = (uu___354_531.defer_ok);
                        smt_ok = (uu___354_531.smt_ok);
                        umax_heuristic_ok = (uu___354_531.umax_heuristic_ok);
                        tcenv = (uu___354_531.tcenv);
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
            let uu___355_564 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___355_564.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___355_564.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___355_564.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___355_564.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___355_564.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___355_564.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___355_564.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___355_564.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___355_564.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___355_564.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___355_564.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___355_564.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___355_564.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___355_564.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___355_564.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___355_564.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___355_564.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___355_564.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___355_564.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___355_564.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___355_564.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___355_564.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___355_564.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___355_564.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___355_564.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___355_564.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___355_564.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___355_564.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___355_564.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___355_564.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___355_564.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___355_564.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___355_564.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___355_564.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___355_564.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___355_564.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___355_564.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___355_564.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___355_564.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___355_564.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___355_564.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___355_564.FStar_TypeChecker_Env.nbe)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____566 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.strcat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____566 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Env.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * Prims.string) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____609 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____646 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * Prims.string)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____680 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____691 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____702 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___322_720  ->
    match uu___322_720 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____732 = FStar_Syntax_Util.head_and_args t  in
    match uu____732 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____795 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____797 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____812 =
                     let uu____814 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____814  in
                   FStar_Util.format1 "@<%s>" uu____812
                in
             let uu____818 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____795 uu____797 uu____818
         | uu____821 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___323_833  ->
      match uu___323_833 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____838 =
            let uu____842 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____844 =
              let uu____848 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____850 =
                let uu____854 =
                  let uu____858 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____858]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____854
                 in
              uu____848 :: uu____850  in
            uu____842 :: uu____844  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____838
      | FStar_TypeChecker_Common.CProb p ->
          let uu____869 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____871 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____873 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____869 uu____871
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____873
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___324_887  ->
      match uu___324_887 with
      | UNIV (u,t) ->
          let x =
            let uu____893 = FStar_Options.hide_uvar_nums ()  in
            if uu____893
            then "?"
            else
              (let uu____900 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____900 FStar_Util.string_of_int)
             in
          let uu____904 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____904
      | TERM (u,t) ->
          let x =
            let uu____911 = FStar_Options.hide_uvar_nums ()  in
            if uu____911
            then "?"
            else
              (let uu____918 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____918 FStar_Util.string_of_int)
             in
          let uu____922 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____922
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____941 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____941 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____962 =
      let uu____966 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____966
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____962 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____985 .
    (FStar_Syntax_Syntax.term * 'Auu____985) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1004 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1025  ->
              match uu____1025 with
              | (x,uu____1032) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1004 (FStar_String.concat " ")
  
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
        (let uu____1075 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1075
         then
           let uu____1080 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1080
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___325_1091  ->
    match uu___325_1091 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1097 .
    'Auu____1097 FStar_TypeChecker_Common.problem ->
      'Auu____1097 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___356_1109 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___356_1109.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___356_1109.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___356_1109.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___356_1109.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___356_1109.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___356_1109.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___356_1109.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1117 .
    'Auu____1117 FStar_TypeChecker_Common.problem ->
      'Auu____1117 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___326_1137  ->
    match uu___326_1137 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_1  -> FStar_TypeChecker_Common.TProb _0_1)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_2  -> FStar_TypeChecker_Common.CProb _0_2)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___327_1153  ->
    match uu___327_1153 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___357_1159 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___357_1159.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___357_1159.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___357_1159.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___357_1159.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___357_1159.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___357_1159.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___357_1159.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___357_1159.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___357_1159.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___358_1167 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___358_1167.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___358_1167.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___358_1167.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___358_1167.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___358_1167.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___358_1167.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___358_1167.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___358_1167.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___358_1167.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___328_1180  ->
      match uu___328_1180 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___329_1187  ->
    match uu___329_1187 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___330_1200  ->
    match uu___330_1200 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___331_1215  ->
    match uu___331_1215 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___332_1230  ->
    match uu___332_1230 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___333_1244  ->
    match uu___333_1244 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___334_1258  ->
    match uu___334_1258 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___335_1270  ->
    match uu___335_1270 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1286 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____1286) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1316 =
          let uu____1318 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1318  in
        if uu____1316
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1355)::bs ->
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
          let uu____1402 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1426 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1426]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1402
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1454 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1478 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1478]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1454
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1525 =
          let uu____1527 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1527  in
        if uu____1525
        then ()
        else
          (let uu____1532 =
             let uu____1535 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1535
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____1532 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____1584 =
          let uu____1586 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1586  in
        if uu____1584
        then ()
        else
          (let uu____1591 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____1591)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____1611 =
        let uu____1613 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____1613  in
      if uu____1611
      then ()
      else
        (let msgf m =
           let uu____1627 =
             let uu____1629 =
               let uu____1631 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.strcat uu____1631 (Prims.strcat "." m)  in
             Prims.strcat "." uu____1629  in
           Prims.strcat msg uu____1627  in
         (let uu____1636 = msgf "scope"  in
          let uu____1639 = p_scope prob  in
          def_scope_wf uu____1636 (p_loc prob) uu____1639);
         (let uu____1651 = msgf "guard"  in
          def_check_scoped uu____1651 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____1658 = msgf "lhs"  in
                def_check_scoped uu____1658 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1661 = msgf "rhs"  in
                def_check_scoped uu____1661 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____1668 = msgf "lhs"  in
                def_check_scoped_comp uu____1668 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1671 = msgf "rhs"  in
                def_check_scoped_comp uu____1671 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___359_1692 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___359_1692.wl_deferred);
          ctr = (uu___359_1692.ctr);
          defer_ok = (uu___359_1692.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___359_1692.umax_heuristic_ok);
          tcenv = (uu___359_1692.tcenv);
          wl_implicits = (uu___359_1692.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1700 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1700 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___360_1723 = empty_worklist env  in
      let uu____1724 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1724;
        wl_deferred = (uu___360_1723.wl_deferred);
        ctr = (uu___360_1723.ctr);
        defer_ok = (uu___360_1723.defer_ok);
        smt_ok = (uu___360_1723.smt_ok);
        umax_heuristic_ok = (uu___360_1723.umax_heuristic_ok);
        tcenv = (uu___360_1723.tcenv);
        wl_implicits = (uu___360_1723.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___361_1747 = wl  in
        {
          attempting = (uu___361_1747.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___361_1747.ctr);
          defer_ok = (uu___361_1747.defer_ok);
          smt_ok = (uu___361_1747.smt_ok);
          umax_heuristic_ok = (uu___361_1747.umax_heuristic_ok);
          tcenv = (uu___361_1747.tcenv);
          wl_implicits = (uu___361_1747.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___362_1775 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___362_1775.wl_deferred);
         ctr = (uu___362_1775.ctr);
         defer_ok = (uu___362_1775.defer_ok);
         smt_ok = (uu___362_1775.smt_ok);
         umax_heuristic_ok = (uu___362_1775.umax_heuristic_ok);
         tcenv = (uu___362_1775.tcenv);
         wl_implicits = (uu___362_1775.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____1789 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____1789 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____1823 = FStar_Syntax_Util.type_u ()  in
            match uu____1823 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____1835 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____1835 with
                 | (uu____1853,tt,wl1) ->
                     let uu____1856 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                     (uu____1856, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___336_1862  ->
    match uu___336_1862 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_3  -> FStar_TypeChecker_Common.TProb _0_3) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_4  -> FStar_TypeChecker_Common.CProb _0_4) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1880 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1880 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1900  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____1997 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____1997 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____1997 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____1997 FStar_TypeChecker_Common.problem *
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
                        let uu____2084 =
                          let uu____2093 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2093]  in
                        FStar_List.append scope uu____2084
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____2136 =
                      let uu____2139 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____2139  in
                    FStar_List.append uu____2136
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____2158 =
                    new_uvar
                      (Prims.strcat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2158 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2184 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2184;
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
                  def_check_prob (Prims.strcat reason ".mk_t.arg") orig;
                  (let uu____2258 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2258 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.strcat reason ".mk_t")
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
                  def_check_prob (Prims.strcat reason ".mk_c.arg") orig;
                  (let uu____2346 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2346 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.strcat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____2384 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2384 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2384 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2384 FStar_TypeChecker_Common.problem *
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
                          let uu____2452 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2452]  in
                        let uu____2471 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____2471
                     in
                  let uu____2474 =
                    let uu____2481 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.strcat "new_problem: logical guard for " reason)
                      (let uu___363_2492 = wl  in
                       {
                         attempting = (uu___363_2492.attempting);
                         wl_deferred = (uu___363_2492.wl_deferred);
                         ctr = (uu___363_2492.ctr);
                         defer_ok = (uu___363_2492.defer_ok);
                         smt_ok = (uu___363_2492.smt_ok);
                         umax_heuristic_ok =
                           (uu___363_2492.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___363_2492.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2481
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2474 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____2510 =
                              let uu____2515 =
                                let uu____2516 =
                                  let uu____2525 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____2525
                                   in
                                [uu____2516]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2515  in
                            uu____2510 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____2555 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2555;
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
                let uu____2603 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2603;
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
  'Auu____2618 .
    worklist ->
      'Auu____2618 FStar_TypeChecker_Common.problem ->
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
              let uu____2651 =
                let uu____2654 =
                  let uu____2655 =
                    let uu____2662 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____2662)  in
                  FStar_Syntax_Syntax.NT uu____2655  in
                [uu____2654]  in
              FStar_Syntax_Subst.subst uu____2651 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____2686 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2686
        then
          let uu____2694 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2697 = prob_to_string env d  in
          let uu____2699 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2694 uu____2697 uu____2699 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2715 -> failwith "impossible"  in
           let uu____2718 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2734 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2736 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2734, uu____2736)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2743 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2745 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2743, uu____2745)
              in
           match uu____2718 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___337_2773  ->
            match uu___337_2773 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2785 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2789 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____2789 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___338_2820  ->
           match uu___338_2820 with
           | UNIV uu____2823 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2830 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2830
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
        (fun uu___339_2858  ->
           match uu___339_2858 with
           | UNIV (u',t) ->
               let uu____2863 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2863
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2870 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2882 =
        let uu____2883 =
          let uu____2884 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____2884
           in
        FStar_Syntax_Subst.compress uu____2883  in
      FStar_All.pipe_right uu____2882 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2896 =
        let uu____2897 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____2897  in
      FStar_All.pipe_right uu____2896 FStar_Syntax_Util.unlazy_emb
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2905 = FStar_Syntax_Util.head_and_args t  in
    match uu____2905 with
    | (h,uu____2924) ->
        let uu____2949 =
          let uu____2950 = FStar_Syntax_Subst.compress h  in
          uu____2950.FStar_Syntax_Syntax.n  in
        (match uu____2949 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____2955 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2968 = should_strongly_reduce t  in
      if uu____2968
      then
        let uu____2971 =
          let uu____2972 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Reify;
              FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant] env t
             in
          FStar_Syntax_Subst.compress uu____2972  in
        FStar_All.pipe_right uu____2971 FStar_Syntax_Util.unlazy_emb
      else whnf' env t
  
let norm_arg :
  'Auu____2982 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____2982) ->
        (FStar_Syntax_Syntax.term * 'Auu____2982)
  =
  fun env  ->
    fun t  ->
      let uu____3005 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____3005, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____3057  ->
              match uu____3057 with
              | (x,imp) ->
                  let uu____3076 =
                    let uu___364_3077 = x  in
                    let uu____3078 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___364_3077.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___364_3077.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3078
                    }  in
                  (uu____3076, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3102 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3102
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3106 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3106
        | uu____3109 -> u2  in
      let uu____3110 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3110
  
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
                (let uu____3231 = norm_refinement env t12  in
                 match uu____3231 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3246;
                     FStar_Syntax_Syntax.vars = uu____3247;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3271 =
                       let uu____3273 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3275 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3273 uu____3275
                        in
                     failwith uu____3271)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3291 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3291
          | FStar_Syntax_Syntax.Tm_uinst uu____3292 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3329 =
                   let uu____3330 = FStar_Syntax_Subst.compress t1'  in
                   uu____3330.FStar_Syntax_Syntax.n  in
                 match uu____3329 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3345 -> aux true t1'
                 | uu____3353 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3368 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3399 =
                   let uu____3400 = FStar_Syntax_Subst.compress t1'  in
                   uu____3400.FStar_Syntax_Syntax.n  in
                 match uu____3399 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3415 -> aux true t1'
                 | uu____3423 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3438 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3485 =
                   let uu____3486 = FStar_Syntax_Subst.compress t1'  in
                   uu____3486.FStar_Syntax_Syntax.n  in
                 match uu____3485 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3501 -> aux true t1'
                 | uu____3509 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3524 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3539 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3554 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3569 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3584 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3613 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3646 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3667 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3694 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3722 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3759 ->
              let uu____3766 =
                let uu____3768 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3770 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3768 uu____3770
                 in
              failwith uu____3766
          | FStar_Syntax_Syntax.Tm_ascribed uu____3785 ->
              let uu____3812 =
                let uu____3814 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3816 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3814 uu____3816
                 in
              failwith uu____3812
          | FStar_Syntax_Syntax.Tm_delayed uu____3831 ->
              let uu____3854 =
                let uu____3856 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3858 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3856 uu____3858
                 in
              failwith uu____3854
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3873 =
                let uu____3875 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3877 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3875 uu____3877
                 in
              failwith uu____3873
           in
        let uu____3892 = whnf env t1  in aux false uu____3892
  
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
      let uu____3953 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3953 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____3994 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3994, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____4021 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____4021 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4081  ->
    match uu____4081 with
    | (t_base,refopt) ->
        let uu____4112 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4112 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4154 =
      let uu____4158 =
        let uu____4161 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4188  ->
                  match uu____4188 with | (uu____4197,uu____4198,x) -> x))
           in
        FStar_List.append wl.attempting uu____4161  in
      FStar_List.map (wl_prob_to_string wl) uu____4158  in
    FStar_All.pipe_right uu____4154 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____4221 .
    ('Auu____4221 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____4233  ->
    match uu____4233 with
    | (uu____4240,c,args) ->
        let uu____4243 = print_ctx_uvar c  in
        let uu____4245 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4243 uu____4245
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4255 = FStar_Syntax_Util.head_and_args t  in
    match uu____4255 with
    | (head1,_args) ->
        let uu____4299 =
          let uu____4300 = FStar_Syntax_Subst.compress head1  in
          uu____4300.FStar_Syntax_Syntax.n  in
        (match uu____4299 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4304 -> true
         | uu____4318 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4326 = FStar_Syntax_Util.head_and_args t  in
    match uu____4326 with
    | (head1,_args) ->
        let uu____4369 =
          let uu____4370 = FStar_Syntax_Subst.compress head1  in
          uu____4370.FStar_Syntax_Syntax.n  in
        (match uu____4369 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4374) -> u
         | uu____4391 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____4416 = FStar_Syntax_Util.head_and_args t  in
      match uu____4416 with
      | (head1,args) ->
          let uu____4463 =
            let uu____4464 = FStar_Syntax_Subst.compress head1  in
            uu____4464.FStar_Syntax_Syntax.n  in
          (match uu____4463 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4472)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4505 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___340_4530  ->
                         match uu___340_4530 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4535 =
                               let uu____4536 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4536.FStar_Syntax_Syntax.n  in
                             (match uu____4535 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4541 -> false)
                         | uu____4543 -> true))
                  in
               (match uu____4505 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4568 =
                        FStar_List.collect
                          (fun uu___341_4580  ->
                             match uu___341_4580 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4584 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4584]
                             | uu____4585 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4568 FStar_List.rev  in
                    let uu____4608 =
                      let uu____4615 =
                        let uu____4624 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___342_4646  ->
                                  match uu___342_4646 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4650 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4650]
                                  | uu____4651 -> []))
                           in
                        FStar_All.pipe_right uu____4624 FStar_List.rev  in
                      let uu____4674 =
                        let uu____4677 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4677  in
                      new_uvar
                        (Prims.strcat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4615 uu____4674
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____4608 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4713  ->
                                match uu____4713 with
                                | (x,i) ->
                                    let uu____4732 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4732, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4763  ->
                                match uu____4763 with
                                | (a,i) ->
                                    let uu____4782 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4782, i)) args_sol
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
           | uu____4804 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4826 =
          let uu____4849 =
            let uu____4850 = FStar_Syntax_Subst.compress k  in
            uu____4850.FStar_Syntax_Syntax.n  in
          match uu____4849 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4932 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____4932)
              else
                (let uu____4967 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4967 with
                 | (ys',t1,uu____5000) ->
                     let uu____5005 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____5005))
          | uu____5044 ->
              let uu____5045 =
                let uu____5050 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5050)  in
              ((ys, t), uu____5045)
           in
        match uu____4826 with
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
                 let uu____5145 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5145 c  in
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
               (let uu____5223 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5223
                then
                  let uu____5228 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5230 = print_ctx_uvar uv  in
                  let uu____5232 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5228 uu____5230 uu____5232
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5241 =
                   let uu____5243 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.strcat "solve_prob'.sol." uu____5243  in
                 let uu____5246 =
                   let uu____5249 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5249
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5241 uu____5246 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____5282 =
               let uu____5283 =
                 let uu____5285 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5287 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5285 uu____5287
                  in
               failwith uu____5283  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5353  ->
                       match uu____5353 with
                       | (a,i) ->
                           let uu____5374 =
                             let uu____5375 = FStar_Syntax_Subst.compress a
                                in
                             uu____5375.FStar_Syntax_Syntax.n  in
                           (match uu____5374 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5401 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____5411 =
                 let uu____5413 = is_flex g  in Prims.op_Negation uu____5413
                  in
               if uu____5411
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____5422 = destruct_flex_t g wl  in
                  match uu____5422 with
                  | ((uu____5427,uv1,args),wl1) ->
                      ((let uu____5432 = args_as_binders args  in
                        assign_solution uu____5432 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___365_5434 = wl1  in
              {
                attempting = (uu___365_5434.attempting);
                wl_deferred = (uu___365_5434.wl_deferred);
                ctr = (wl1.ctr + (Prims.parse_int "1"));
                defer_ok = (uu___365_5434.defer_ok);
                smt_ok = (uu___365_5434.smt_ok);
                umax_heuristic_ok = (uu___365_5434.umax_heuristic_ok);
                tcenv = (uu___365_5434.tcenv);
                wl_implicits = (uu___365_5434.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5459 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5459
         then
           let uu____5464 = FStar_Util.string_of_int pid  in
           let uu____5466 =
             let uu____5468 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____5468 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5464 uu____5466
         else ());
        commit sol;
        (let uu___366_5482 = wl  in
         {
           attempting = (uu___366_5482.attempting);
           wl_deferred = (uu___366_5482.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___366_5482.defer_ok);
           smt_ok = (uu___366_5482.smt_ok);
           umax_heuristic_ok = (uu___366_5482.umax_heuristic_ok);
           tcenv = (uu___366_5482.tcenv);
           wl_implicits = (uu___366_5482.wl_implicits)
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
             | (uu____5548,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____5576 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____5576
              in
           (let uu____5582 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____5582
            then
              let uu____5587 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____5591 =
                let uu____5593 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____5593 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____5587 uu____5591
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
        let uu____5628 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5628 FStar_Util.set_elements  in
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
      let uu____5668 = occurs uk t  in
      match uu____5668 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5707 =
                 let uu____5709 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5711 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5709 uu____5711
                  in
               FStar_Pervasives_Native.Some uu____5707)
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
            let uu____5831 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5831 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5882 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5939  ->
             match uu____5939 with
             | (x,uu____5951) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____5969 = FStar_List.last bs  in
      match uu____5969 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____5993) ->
          let uu____6004 =
            FStar_Util.prefix_until
              (fun uu___343_6019  ->
                 match uu___343_6019 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6022 -> false) g
             in
          (match uu____6004 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6036,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6073 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6073 with
        | (pfx,uu____6083) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6095 =
              new_uvar
                (Prims.strcat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6095 with
             | (uu____6103,src',wl1) ->
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
                 | uu____6217 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6218 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6282  ->
                  fun uu____6283  ->
                    match (uu____6282, uu____6283) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6386 =
                          let uu____6388 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6388
                           in
                        if uu____6386
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6422 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6422
                           then
                             let uu____6439 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6439)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6218 with | (isect,uu____6489) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____6525 'Auu____6526 .
    (FStar_Syntax_Syntax.bv * 'Auu____6525) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____6526) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6584  ->
              fun uu____6585  ->
                match (uu____6584, uu____6585) with
                | ((a,uu____6604),(b,uu____6606)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____6622 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____6622) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6653  ->
           match uu____6653 with
           | (y,uu____6660) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6670 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____6670) Prims.list ->
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
                   let uu____6832 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6832
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6865 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6917 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____6962 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____6984 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___344_6992  ->
    match uu___344_6992 with
    | MisMatch (d1,d2) ->
        let uu____7004 =
          let uu____7006 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7008 =
            let uu____7010 =
              let uu____7012 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____7012 ")"  in
            Prims.strcat ") (" uu____7010  in
          Prims.strcat uu____7006 uu____7008  in
        Prims.strcat "MisMatch (" uu____7004
    | HeadMatch u ->
        let uu____7019 = FStar_Util.string_of_bool u  in
        Prims.strcat "HeadMatch " uu____7019
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___345_7028  ->
    match uu___345_7028 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7045 -> HeadMatch false
  
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
          let uu____7067 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7067 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7078 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7102 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7112 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7139 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7139
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7140 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7141 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7142 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7155 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7169 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7193) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7199,uu____7200) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7242) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7267;
             FStar_Syntax_Syntax.index = uu____7268;
             FStar_Syntax_Syntax.sort = t2;_},uu____7270)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7278 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7279 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7280 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7295 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7302 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7322 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7322
  
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
           { FStar_Syntax_Syntax.blob = uu____7341;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7342;
             FStar_Syntax_Syntax.ltyp = uu____7343;
             FStar_Syntax_Syntax.rng = uu____7344;_},uu____7345)
            ->
            let uu____7356 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7356 t21
        | (uu____7357,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7358;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7359;
             FStar_Syntax_Syntax.ltyp = uu____7360;
             FStar_Syntax_Syntax.rng = uu____7361;_})
            ->
            let uu____7372 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7372
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7384 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7384
            then FullMatch
            else
              (let uu____7389 =
                 let uu____7398 =
                   let uu____7401 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7401  in
                 let uu____7402 =
                   let uu____7405 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7405  in
                 (uu____7398, uu____7402)  in
               MisMatch uu____7389)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7411),FStar_Syntax_Syntax.Tm_uinst (g,uu____7413)) ->
            let uu____7422 = head_matches env f g  in
            FStar_All.pipe_right uu____7422 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7423) -> HeadMatch true
        | (uu____7425,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7429 = FStar_Const.eq_const c d  in
            if uu____7429
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7439),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7441)) ->
            let uu____7474 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7474
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7484),FStar_Syntax_Syntax.Tm_refine (y,uu____7486)) ->
            let uu____7495 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7495 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____7497),uu____7498) ->
            let uu____7503 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____7503 head_match
        | (uu____7504,FStar_Syntax_Syntax.Tm_refine (x,uu____7506)) ->
            let uu____7511 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7511 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7512,FStar_Syntax_Syntax.Tm_type
           uu____7513) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____7515,FStar_Syntax_Syntax.Tm_arrow uu____7516) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____7547),FStar_Syntax_Syntax.Tm_app (head',uu____7549))
            ->
            let uu____7598 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____7598 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____7600),uu____7601) ->
            let uu____7626 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____7626 head_match
        | (uu____7627,FStar_Syntax_Syntax.Tm_app (head1,uu____7629)) ->
            let uu____7654 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____7654 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7655,FStar_Syntax_Syntax.Tm_let
           uu____7656) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____7684,FStar_Syntax_Syntax.Tm_match uu____7685) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7731,FStar_Syntax_Syntax.Tm_abs
           uu____7732) -> HeadMatch true
        | uu____7770 ->
            let uu____7775 =
              let uu____7784 = delta_depth_of_term env t11  in
              let uu____7787 = delta_depth_of_term env t21  in
              (uu____7784, uu____7787)  in
            MisMatch uu____7775
  
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
            let head1 = FStar_Syntax_Util.head_of t  in
            (let uu____7853 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7853
             then
               let uu____7858 = FStar_Syntax_Print.term_to_string t  in
               let uu____7860 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7858 uu____7860
             else ());
            (let uu____7865 =
               let uu____7866 = FStar_Syntax_Util.un_uinst head1  in
               uu____7866.FStar_Syntax_Syntax.n  in
             match uu____7865 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7872 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7872 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7886 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7886
                        then
                          let uu____7891 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7891
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7896 ->
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
                      let uu____7913 =
                        let uu____7915 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____7915 = FStar_Syntax_Util.Equal  in
                      if uu____7913
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____7922 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____7922
                          then
                            let uu____7927 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____7929 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____7927
                              uu____7929
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____7934 -> FStar_Pervasives_Native.None)
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
            (let uu____8086 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8086
             then
               let uu____8091 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8093 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8095 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8091
                 uu____8093 uu____8095
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8123 =
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
               match uu____8123 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____8171 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8171 with
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
                  uu____8209),uu____8210)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8231 =
                      let uu____8240 = maybe_inline t11  in
                      let uu____8243 = maybe_inline t21  in
                      (uu____8240, uu____8243)  in
                    match uu____8231 with
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
                 (uu____8286,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8287))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8308 =
                      let uu____8317 = maybe_inline t11  in
                      let uu____8320 = maybe_inline t21  in
                      (uu____8317, uu____8320)  in
                    match uu____8308 with
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
             | MisMatch uu____8375 -> fail1 n_delta r t11 t21
             | uu____8384 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____8399 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8399
           then
             let uu____8404 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8406 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8408 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8416 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8433 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8433
                    (fun uu____8468  ->
                       match uu____8468 with
                       | (t11,t21) ->
                           let uu____8476 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8478 =
                             let uu____8480 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.strcat "; " uu____8480  in
                           Prims.strcat uu____8476 uu____8478))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8404 uu____8406 uu____8408 uu____8416
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____8497 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____8497 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___346_8512  ->
    match uu___346_8512 with
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
      let uu___367_8561 = p  in
      let uu____8564 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8565 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___367_8561.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8564;
        FStar_TypeChecker_Common.relation =
          (uu___367_8561.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8565;
        FStar_TypeChecker_Common.element =
          (uu___367_8561.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___367_8561.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___367_8561.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___367_8561.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___367_8561.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___367_8561.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8580 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____8580
            (fun _0_5  -> FStar_TypeChecker_Common.TProb _0_5)
      | FStar_TypeChecker_Common.CProb uu____8585 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____8608 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____8608 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8616 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8616 with
           | (lh,lhs_args) ->
               let uu____8663 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8663 with
                | (rh,rhs_args) ->
                    let uu____8710 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8723,FStar_Syntax_Syntax.Tm_uvar uu____8724)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8813 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8840,uu____8841)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8856,FStar_Syntax_Syntax.Tm_uvar uu____8857)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8872,FStar_Syntax_Syntax.Tm_arrow uu____8873)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___368_8903 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___368_8903.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___368_8903.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___368_8903.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___368_8903.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___368_8903.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___368_8903.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___368_8903.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___368_8903.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___368_8903.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8906,FStar_Syntax_Syntax.Tm_type uu____8907)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___368_8923 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___368_8923.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___368_8923.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___368_8923.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___368_8923.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___368_8923.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___368_8923.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___368_8923.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___368_8923.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___368_8923.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____8926,FStar_Syntax_Syntax.Tm_uvar uu____8927)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___368_8943 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___368_8943.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___368_8943.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___368_8943.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___368_8943.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___368_8943.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___368_8943.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___368_8943.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___368_8943.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___368_8943.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____8946,FStar_Syntax_Syntax.Tm_uvar uu____8947)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8962,uu____8963)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8978,FStar_Syntax_Syntax.Tm_uvar uu____8979)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8994,uu____8995) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____8710 with
                     | (rank,tp1) ->
                         let uu____9008 =
                           FStar_All.pipe_right
                             (let uu___369_9012 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___369_9012.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___369_9012.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___369_9012.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___369_9012.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___369_9012.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___369_9012.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___369_9012.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___369_9012.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___369_9012.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_6  ->
                                FStar_TypeChecker_Common.TProb _0_6)
                            in
                         (rank, uu____9008))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9018 =
            FStar_All.pipe_right
              (let uu___370_9022 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___370_9022.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___370_9022.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___370_9022.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___370_9022.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___370_9022.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___370_9022.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___370_9022.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___370_9022.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___370_9022.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_7  -> FStar_TypeChecker_Common.CProb _0_7)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9018)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9084 probs =
      match uu____9084 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9165 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____9186 = rank wl.tcenv hd1  in
               (match uu____9186 with
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
                      (let uu____9247 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9252 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9252)
                          in
                       if uu____9247
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
          let uu____9325 = FStar_Syntax_Util.head_and_args t  in
          match uu____9325 with
          | (hd1,uu____9344) ->
              let uu____9369 =
                let uu____9370 = FStar_Syntax_Subst.compress hd1  in
                uu____9370.FStar_Syntax_Syntax.n  in
              (match uu____9369 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9375) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9410  ->
                           match uu____9410 with
                           | (y,uu____9419) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9442  ->
                                       match uu____9442 with
                                       | (x,uu____9451) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9456 -> false)
           in
        let uu____9458 = rank tcenv p  in
        match uu____9458 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9467 -> true
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
    match projectee with | UDeferred _0 -> true | uu____9504 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9524 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9545 -> false
  
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
                        let uu____9608 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9608 with
                        | (k,uu____9616) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9629 -> false)))
            | uu____9631 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9683 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9691 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9691 = (Prims.parse_int "0")))
                           in
                        if uu____9683 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9712 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9720 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9720 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____9712)
               in
            let uu____9724 = filter1 u12  in
            let uu____9727 = filter1 u22  in (uu____9724, uu____9727)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then UFailed "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9762 = filter_out_common_univs us1 us2  in
                   (match uu____9762 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____9822 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____9822 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9825 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          (let uu____9836 =
                             let uu____9838 =
                               FStar_Syntax_Print.univ_to_string u12  in
                             let uu____9840 =
                               FStar_Syntax_Print.univ_to_string u22  in
                             FStar_Util.format2
                               "Unable to unify universes: %s and %s"
                               uu____9838 uu____9840
                              in
                           UFailed uu____9836))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9866 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____9866 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9892 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____9892 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____9895 ->
                   let uu____9900 =
                     let uu____9902 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____9904 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format3
                       "Unable to unify universes: %s and %s (%s)" uu____9902
                       uu____9904 msg
                      in
                   UFailed uu____9900)
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9907,uu____9908) ->
              let uu____9910 =
                let uu____9912 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9914 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9912 uu____9914
                 in
              failwith uu____9910
          | (FStar_Syntax_Syntax.U_unknown ,uu____9917) ->
              let uu____9918 =
                let uu____9920 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9922 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9920 uu____9922
                 in
              failwith uu____9918
          | (uu____9925,FStar_Syntax_Syntax.U_bvar uu____9926) ->
              let uu____9928 =
                let uu____9930 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9932 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9930 uu____9932
                 in
              failwith uu____9928
          | (uu____9935,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9936 =
                let uu____9938 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9940 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9938 uu____9940
                 in
              failwith uu____9936
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9970 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____9970
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____9987 = occurs_univ v1 u3  in
              if uu____9987
              then
                let uu____9990 =
                  let uu____9992 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9994 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9992 uu____9994
                   in
                try_umax_components u11 u21 uu____9990
              else
                (let uu____9999 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9999)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10011 = occurs_univ v1 u3  in
              if uu____10011
              then
                let uu____10014 =
                  let uu____10016 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10018 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10016 uu____10018
                   in
                try_umax_components u11 u21 uu____10014
              else
                (let uu____10023 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10023)
          | (FStar_Syntax_Syntax.U_max uu____10024,uu____10025) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10033 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10033
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10039,FStar_Syntax_Syntax.U_max uu____10040) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10048 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10048
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10054,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10056,FStar_Syntax_Syntax.U_name uu____10057) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10059) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10061) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10063,FStar_Syntax_Syntax.U_succ uu____10064) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10066,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10173 = bc1  in
      match uu____10173 with
      | (bs1,mk_cod1) ->
          let uu____10217 = bc2  in
          (match uu____10217 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10328 = aux xs ys  in
                     (match uu____10328 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10411 =
                       let uu____10418 = mk_cod1 xs  in ([], uu____10418)  in
                     let uu____10421 =
                       let uu____10428 = mk_cod2 ys  in ([], uu____10428)  in
                     (uu____10411, uu____10421)
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
                  let uu____10497 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10497 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____10500 =
                    let uu____10501 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____10501 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____10500
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____10506 = has_type_guard t1 t2  in (uu____10506, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____10507 = has_type_guard t2 t1  in (uu____10507, wl)
  
let is_flex_pat :
  'Auu____10517 'Auu____10518 'Auu____10519 .
    ('Auu____10517 * 'Auu____10518 * 'Auu____10519 Prims.list) -> Prims.bool
  =
  fun uu___347_10533  ->
    match uu___347_10533 with
    | (uu____10542,uu____10543,[]) -> true
    | uu____10547 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____10580 = f  in
      match uu____10580 with
      | (uu____10587,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____10588;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10589;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____10592;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____10593;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____10594;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____10595;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10665  ->
                 match uu____10665 with
                 | (y,uu____10674) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____10828 =
                  let uu____10843 =
                    let uu____10846 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____10846  in
                  ((FStar_List.rev pat_binders), uu____10843)  in
                FStar_Pervasives_Native.Some uu____10828
            | (uu____10879,[]) ->
                let uu____10910 =
                  let uu____10925 =
                    let uu____10928 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____10928  in
                  ((FStar_List.rev pat_binders), uu____10925)  in
                FStar_Pervasives_Native.Some uu____10910
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11019 =
                  let uu____11020 = FStar_Syntax_Subst.compress a  in
                  uu____11020.FStar_Syntax_Syntax.n  in
                (match uu____11019 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11040 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11040
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___371_11070 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___371_11070.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___371_11070.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____11074 =
                            let uu____11075 =
                              let uu____11082 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11082)  in
                            FStar_Syntax_Syntax.NT uu____11075  in
                          [uu____11074]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___372_11098 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___372_11098.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___372_11098.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11099 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11139 =
                  let uu____11154 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11154  in
                (match uu____11139 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11229 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11262 ->
               let uu____11263 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11263 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____11585 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____11585
       then
         let uu____11590 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11590
       else ());
      (let uu____11595 = next_prob probs  in
       match uu____11595 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___373_11622 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___373_11622.wl_deferred);
               ctr = (uu___373_11622.ctr);
               defer_ok = (uu___373_11622.defer_ok);
               smt_ok = (uu___373_11622.smt_ok);
               umax_heuristic_ok = (uu___373_11622.umax_heuristic_ok);
               tcenv = (uu___373_11622.tcenv);
               wl_implicits = (uu___373_11622.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11631 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____11631
                 then
                   let uu____11634 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____11634
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
                           (let uu___374_11646 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___374_11646.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___374_11646.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___374_11646.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___374_11646.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___374_11646.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___374_11646.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___374_11646.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___374_11646.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___374_11646.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____11672 ->
                let uu____11683 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11754  ->
                          match uu____11754 with
                          | (c,uu____11765,uu____11766) -> c < probs.ctr))
                   in
                (match uu____11683 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11821 =
                            let uu____11826 =
                              FStar_List.map
                                (fun uu____11844  ->
                                   match uu____11844 with
                                   | (uu____11858,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____11826, (probs.wl_implicits))  in
                          Success uu____11821
                      | uu____11866 ->
                          let uu____11877 =
                            let uu___375_11878 = probs  in
                            let uu____11879 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____11902  ->
                                      match uu____11902 with
                                      | (uu____11911,uu____11912,y) -> y))
                               in
                            {
                              attempting = uu____11879;
                              wl_deferred = rest;
                              ctr = (uu___375_11878.ctr);
                              defer_ok = (uu___375_11878.defer_ok);
                              smt_ok = (uu___375_11878.smt_ok);
                              umax_heuristic_ok =
                                (uu___375_11878.umax_heuristic_ok);
                              tcenv = (uu___375_11878.tcenv);
                              wl_implicits = (uu___375_11878.wl_implicits)
                            }  in
                          solve env uu____11877))))

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
            let uu____11923 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____11923 with
            | USolved wl1 ->
                let uu____11925 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____11925
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
                  let uu____11979 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____11979 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____11982 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____11995;
                  FStar_Syntax_Syntax.vars = uu____11996;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____11999;
                  FStar_Syntax_Syntax.vars = uu____12000;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12013,uu____12014) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12022,FStar_Syntax_Syntax.Tm_uinst uu____12023) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12031 -> USolved wl

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
            ((let uu____12043 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12043
              then
                let uu____12048 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12048 msg
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
               let uu____12140 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12140 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12195 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12195
                then
                  let uu____12200 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12202 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12200 uu____12202
                else ());
               (let uu____12207 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12207 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12253 = eq_prob t1 t2 wl2  in
                         (match uu____12253 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12274 ->
                         let uu____12283 = eq_prob t1 t2 wl2  in
                         (match uu____12283 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____12333 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____12348 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____12349 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____12348, uu____12349)
                           | FStar_Pervasives_Native.None  ->
                               let uu____12354 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____12355 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____12354, uu____12355)
                            in
                         (match uu____12333 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12386 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____12386 with
                                | (t1_hd,t1_args) ->
                                    let uu____12431 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____12431 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12497 =
                                              let uu____12504 =
                                                let uu____12515 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____12515 :: t1_args  in
                                              let uu____12532 =
                                                let uu____12541 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____12541 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____12590  ->
                                                   fun uu____12591  ->
                                                     fun uu____12592  ->
                                                       match (uu____12590,
                                                               uu____12591,
                                                               uu____12592)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____12642),
                                                          (a2,uu____12644))
                                                           ->
                                                           let uu____12681 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____12681
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12504
                                                uu____12532
                                               in
                                            match uu____12497 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___376_12707 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___376_12707.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___376_12707.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___376_12707.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12719 =
                                                  solve env1 wl'  in
                                                (match uu____12719 with
                                                 | Success (uu____12722,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___377_12726
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___377_12726.attempting);
                                                            wl_deferred =
                                                              (uu___377_12726.wl_deferred);
                                                            ctr =
                                                              (uu___377_12726.ctr);
                                                            defer_ok =
                                                              (uu___377_12726.defer_ok);
                                                            smt_ok =
                                                              (uu___377_12726.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___377_12726.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___377_12726.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____12727 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____12760 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____12760 with
                                | (t1_base,p1_opt) ->
                                    let uu____12796 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____12796 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____12895 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____12895
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
                                               let uu____12948 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____12948
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
                                               let uu____12980 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____12980
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
                                               let uu____13012 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13012
                                           | uu____13015 -> t_base  in
                                         let uu____13032 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13032 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13046 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13046, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13053 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13053 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13089 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13089 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13125 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13125
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
                              let uu____13149 = combine t11 t21 wl2  in
                              (match uu____13149 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13182 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13182
                                     then
                                       let uu____13187 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13187
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13229 ts1 =
               match uu____13229 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13292 = pairwise out t wl2  in
                        (match uu____13292 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____13328 =
               let uu____13339 = FStar_List.hd ts  in (uu____13339, [], wl1)
                in
             let uu____13348 = FStar_List.tl ts  in
             aux uu____13328 uu____13348  in
           let uu____13355 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____13355 with
           | (this_flex,this_rigid) ->
               let uu____13381 =
                 let uu____13382 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____13382.FStar_Syntax_Syntax.n  in
               (match uu____13381 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____13407 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____13407
                    then
                      let uu____13410 = destruct_flex_t this_flex wl  in
                      (match uu____13410 with
                       | (flex,wl1) ->
                           let uu____13417 = quasi_pattern env flex  in
                           (match uu____13417 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____13436 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____13436
                                  then
                                    let uu____13441 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13441
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13448 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___378_13451 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___378_13451.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___378_13451.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___378_13451.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___378_13451.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___378_13451.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___378_13451.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___378_13451.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___378_13451.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___378_13451.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____13448)
                | uu____13452 ->
                    ((let uu____13454 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13454
                      then
                        let uu____13459 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13459
                      else ());
                     (let uu____13464 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____13464 with
                      | (u,_args) ->
                          let uu____13507 =
                            let uu____13508 = FStar_Syntax_Subst.compress u
                               in
                            uu____13508.FStar_Syntax_Syntax.n  in
                          (match uu____13507 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____13536 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____13536 with
                                 | (u',uu____13555) ->
                                     let uu____13580 =
                                       let uu____13581 = whnf env u'  in
                                       uu____13581.FStar_Syntax_Syntax.n  in
                                     (match uu____13580 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13603 -> false)
                                  in
                               let uu____13605 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___348_13628  ->
                                         match uu___348_13628 with
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
                                              | uu____13642 -> false)
                                         | uu____13646 -> false))
                                  in
                               (match uu____13605 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____13661 = whnf env this_rigid
                                         in
                                      let uu____13662 =
                                        FStar_List.collect
                                          (fun uu___349_13668  ->
                                             match uu___349_13668 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13674 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____13674]
                                             | uu____13678 -> [])
                                          bounds_probs
                                         in
                                      uu____13661 :: uu____13662  in
                                    let uu____13679 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____13679 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____13712 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____13727 =
                                               let uu____13728 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____13728.FStar_Syntax_Syntax.n
                                                in
                                             match uu____13727 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13740 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13740)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13751 -> bound  in
                                           let uu____13752 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____13752)  in
                                         (match uu____13712 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13787 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____13787
                                                then
                                                  let wl'1 =
                                                    let uu___379_13793 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___379_13793.wl_deferred);
                                                      ctr =
                                                        (uu___379_13793.ctr);
                                                      defer_ok =
                                                        (uu___379_13793.defer_ok);
                                                      smt_ok =
                                                        (uu___379_13793.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___379_13793.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___379_13793.tcenv);
                                                      wl_implicits =
                                                        (uu___379_13793.wl_implicits)
                                                    }  in
                                                  let uu____13794 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13794
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13800 =
                                                  solve_t env eq_prob
                                                    (let uu___380_13802 = wl'
                                                        in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___380_13802.wl_deferred);
                                                       ctr =
                                                         (uu___380_13802.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___380_13802.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___380_13802.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___380_13802.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____13800 with
                                                | Success (uu____13804,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___381_13807 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___381_13807.wl_deferred);
                                                        ctr =
                                                          (uu___381_13807.ctr);
                                                        defer_ok =
                                                          (uu___381_13807.defer_ok);
                                                        smt_ok =
                                                          (uu___381_13807.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___381_13807.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___381_13807.tcenv);
                                                        wl_implicits =
                                                          (uu___381_13807.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___382_13809 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___382_13809.attempting);
                                                        wl_deferred =
                                                          (uu___382_13809.wl_deferred);
                                                        ctr =
                                                          (uu___382_13809.ctr);
                                                        defer_ok =
                                                          (uu___382_13809.defer_ok);
                                                        smt_ok =
                                                          (uu___382_13809.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___382_13809.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___382_13809.tcenv);
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
                                                    let uu____13825 =
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
                                                    ((let uu____13839 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____13839
                                                      then
                                                        let uu____13844 =
                                                          let uu____13846 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____13846
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13844
                                                      else ());
                                                     (let uu____13859 =
                                                        let uu____13874 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____13874)
                                                         in
                                                      match uu____13859 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____13896))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13922 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____13922
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
                                                                  let uu____13942
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____13942))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13967 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____13967
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
                                                                    let uu____13987
                                                                    =
                                                                    let uu____13992
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____13992
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____13987
                                                                    [] wl2
                                                                     in
                                                                  let uu____13998
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____13998))))
                                                      | uu____13999 ->
                                                          giveup env
                                                            (Prims.strcat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____14015 when flip ->
                               let uu____14016 =
                                 let uu____14018 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14020 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14018 uu____14020
                                  in
                               failwith uu____14016
                           | uu____14023 ->
                               let uu____14024 =
                                 let uu____14026 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14028 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14026 uu____14028
                                  in
                               failwith uu____14024)))))

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
                      (fun uu____14064  ->
                         match uu____14064 with
                         | (x,i) ->
                             let uu____14083 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14083, i)) bs_lhs
                     in
                  let uu____14086 = lhs  in
                  match uu____14086 with
                  | (uu____14087,u_lhs,uu____14089) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14186 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14196 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14196, univ)
                             in
                          match uu____14186 with
                          | (k,univ) ->
                              let uu____14203 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14203 with
                               | (uu____14220,u,wl3) ->
                                   let uu____14223 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14223, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14249 =
                              let uu____14262 =
                                let uu____14273 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14273 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____14324  ->
                                   fun uu____14325  ->
                                     match (uu____14324, uu____14325) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____14426 =
                                           let uu____14433 =
                                             let uu____14436 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____14436
                                              in
                                           copy_uvar u_lhs [] uu____14433 wl2
                                            in
                                         (match uu____14426 with
                                          | (uu____14465,t_a,wl3) ->
                                              let uu____14468 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____14468 with
                                               | (uu____14487,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14262
                                ([], wl1)
                               in
                            (match uu____14249 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___383_14543 = ct  in
                                   let uu____14544 =
                                     let uu____14547 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14547
                                      in
                                   let uu____14562 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___383_14543.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___383_14543.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14544;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14562;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___383_14543.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___384_14580 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___384_14580.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___384_14580.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14583 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____14583 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14645 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14645 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____14656 =
                                          let uu____14661 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____14661)  in
                                        TERM uu____14656  in
                                      let uu____14662 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____14662 with
                                       | (sub_prob,wl3) ->
                                           let uu____14676 =
                                             let uu____14677 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____14677
                                              in
                                           solve env uu____14676))
                             | (x,imp)::formals2 ->
                                 let uu____14699 =
                                   let uu____14706 =
                                     let uu____14709 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____14709
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14706 wl1
                                    in
                                 (match uu____14699 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____14730 =
                                          let uu____14733 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14733
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14730 u_x
                                         in
                                      let uu____14734 =
                                        let uu____14737 =
                                          let uu____14740 =
                                            let uu____14741 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____14741, imp)  in
                                          [uu____14740]  in
                                        FStar_List.append bs_terms
                                          uu____14737
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14734 formals2 wl2)
                              in
                           let uu____14768 = occurs_check u_lhs arrow1  in
                           (match uu____14768 with
                            | (uu____14781,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14797 =
                                    let uu____14799 = FStar_Option.get msg
                                       in
                                    Prims.strcat "occurs-check failed: "
                                      uu____14799
                                     in
                                  giveup_or_defer env orig wl uu____14797
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
              (let uu____14832 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____14832
               then
                 let uu____14837 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____14840 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14837 (rel_to_string (p_rel orig)) uu____14840
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____14967 = rhs wl1 scope env1 subst1  in
                     (match uu____14967 with
                      | (rhs_prob,wl2) ->
                          ((let uu____14988 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____14988
                            then
                              let uu____14993 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____14993
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15071 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15071 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___385_15073 = hd1  in
                       let uu____15074 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___385_15073.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___385_15073.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15074
                       }  in
                     let hd21 =
                       let uu___386_15078 = hd2  in
                       let uu____15079 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___386_15078.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___386_15078.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15079
                       }  in
                     let uu____15082 =
                       let uu____15087 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15087
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15082 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____15108 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____15108
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15115 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____15115 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15182 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15182
                                  in
                               ((let uu____15200 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15200
                                 then
                                   let uu____15205 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15207 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15205
                                     uu____15207
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____15240 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15276 = aux wl [] env [] bs1 bs2  in
               match uu____15276 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15331 = attempt sub_probs wl2  in
                   solve env uu____15331)

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
            let uu___387_15352 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___387_15352.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___387_15352.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15365 = try_solve env wl'  in
          match uu____15365 with
          | Success (uu____15366,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___388_15370 = wl  in
                  {
                    attempting = (uu___388_15370.attempting);
                    wl_deferred = (uu___388_15370.wl_deferred);
                    ctr = (uu___388_15370.ctr);
                    defer_ok = (uu___388_15370.defer_ok);
                    smt_ok = (uu___388_15370.smt_ok);
                    umax_heuristic_ok = (uu___388_15370.umax_heuristic_ok);
                    tcenv = (uu___388_15370.tcenv);
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
        (let uu____15382 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15382 wl)

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
              let uu____15396 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15396 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15430 = lhs1  in
              match uu____15430 with
              | (uu____15433,ctx_u,uu____15435) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15443 ->
                        let uu____15444 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15444 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15493 = quasi_pattern env1 lhs1  in
              match uu____15493 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15527) ->
                  let uu____15532 = lhs1  in
                  (match uu____15532 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15547 = occurs_check ctx_u rhs1  in
                       (match uu____15547 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15598 =
                                let uu____15606 =
                                  let uu____15608 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15608
                                   in
                                FStar_Util.Inl uu____15606  in
                              (uu____15598, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15636 =
                                 let uu____15638 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15638  in
                               if uu____15636
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15665 =
                                    let uu____15673 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15673  in
                                  let uu____15679 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____15665, uu____15679)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____15723 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____15723 with
              | (rhs_hd,args) ->
                  let uu____15766 = FStar_Util.prefix args  in
                  (match uu____15766 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15838 = lhs1  in
                       (match uu____15838 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____15842 =
                              let uu____15853 =
                                let uu____15860 =
                                  let uu____15863 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____15863
                                   in
                                copy_uvar u_lhs [] uu____15860 wl1  in
                              match uu____15853 with
                              | (uu____15890,t_last_arg,wl2) ->
                                  let uu____15893 =
                                    let uu____15900 =
                                      let uu____15901 =
                                        let uu____15910 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____15910]  in
                                      FStar_List.append bs_lhs uu____15901
                                       in
                                    copy_uvar u_lhs uu____15900 t_res_lhs wl2
                                     in
                                  (match uu____15893 with
                                   | (uu____15945,lhs',wl3) ->
                                       let uu____15948 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____15948 with
                                        | (uu____15965,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____15842 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____15986 =
                                     let uu____15987 =
                                       let uu____15992 =
                                         let uu____15993 =
                                           let uu____15996 =
                                             let uu____16001 =
                                               let uu____16002 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____16002]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____16001
                                              in
                                           uu____15996
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____15993
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____15992)  in
                                     TERM uu____15987  in
                                   [uu____15986]  in
                                 let uu____16029 =
                                   let uu____16036 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____16036 with
                                   | (p1,wl3) ->
                                       let uu____16056 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____16056 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____16029 with
                                  | (sub_probs,wl3) ->
                                      let uu____16088 =
                                        let uu____16089 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____16089  in
                                      solve env1 uu____16088))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16123 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16123 with
                | (uu____16141,args) ->
                    (match args with | [] -> false | uu____16177 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16196 =
                  let uu____16197 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16197.FStar_Syntax_Syntax.n  in
                match uu____16196 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16201 -> true
                | uu____16217 -> false  in
              let uu____16219 = quasi_pattern env1 lhs1  in
              match uu____16219 with
              | FStar_Pervasives_Native.None  ->
                  let uu____16230 =
                    let uu____16232 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                      uu____16232
                     in
                  giveup_or_defer env1 orig1 wl1 uu____16230
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16241 = is_app rhs1  in
                  if uu____16241
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____16246 = is_arrow rhs1  in
                     if uu____16246
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____16251 =
                          let uu____16253 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heuristic cannot solve %s; rhs not an app or arrow"
                            uu____16253
                           in
                        giveup_or_defer env1 orig1 wl1 uu____16251))
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
                let uu____16264 = lhs  in
                (match uu____16264 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16268 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16268 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16286 =
                              let uu____16290 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16290
                               in
                            FStar_All.pipe_right uu____16286
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16311 = occurs_check ctx_uv rhs1  in
                          (match uu____16311 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16340 =
                                   let uu____16342 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____16342
                                    in
                                 giveup_or_defer env orig wl uu____16340
                               else
                                 (let uu____16348 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____16348
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____16355 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____16355
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____16359 =
                                         let uu____16361 =
                                           names_to_string1 fvs2  in
                                         let uu____16363 =
                                           names_to_string1 fvs1  in
                                         let uu____16365 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____16361 uu____16363
                                           uu____16365
                                          in
                                       giveup_or_defer env orig wl
                                         uu____16359)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16377 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____16384 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16384 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16410 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16410
                             | (FStar_Util.Inl msg,uu____16412) ->
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
                  (let uu____16457 =
                     let uu____16474 = quasi_pattern env lhs  in
                     let uu____16481 = quasi_pattern env rhs  in
                     (uu____16474, uu____16481)  in
                   match uu____16457 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16524 = lhs  in
                       (match uu____16524 with
                        | ({ FStar_Syntax_Syntax.n = uu____16525;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____16527;_},u_lhs,uu____16529)
                            ->
                            let uu____16532 = rhs  in
                            (match uu____16532 with
                             | (uu____16533,u_rhs,uu____16535) ->
                                 let uu____16536 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16536
                                 then
                                   let uu____16543 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16543
                                 else
                                   (let uu____16546 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16546 with
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
                                        let uu____16578 =
                                          let uu____16585 =
                                            let uu____16588 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16588
                                             in
                                          new_uvar
                                            (Prims.strcat "flex-flex quasi:"
                                               (Prims.strcat "\tlhs="
                                                  (Prims.strcat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.strcat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16585
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____16578 with
                                         | (uu____16600,w,wl1) ->
                                             let w_app =
                                               let uu____16606 =
                                                 let uu____16611 =
                                                   FStar_List.map
                                                     (fun uu____16622  ->
                                                        match uu____16622
                                                        with
                                                        | (z,uu____16630) ->
                                                            let uu____16635 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____16635) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____16611
                                                  in
                                               uu____16606
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16639 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16639
                                               then
                                                 let uu____16644 =
                                                   let uu____16648 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16650 =
                                                     let uu____16654 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____16656 =
                                                       let uu____16660 =
                                                         term_to_string w  in
                                                       let uu____16662 =
                                                         let uu____16666 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____16675 =
                                                           let uu____16679 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____16688 =
                                                             let uu____16692
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____16692]
                                                              in
                                                           uu____16679 ::
                                                             uu____16688
                                                            in
                                                         uu____16666 ::
                                                           uu____16675
                                                          in
                                                       uu____16660 ::
                                                         uu____16662
                                                        in
                                                     uu____16654 ::
                                                       uu____16656
                                                      in
                                                   uu____16648 :: uu____16650
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16644
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____16709 =
                                                     let uu____16714 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____16714)  in
                                                   TERM uu____16709  in
                                                 let uu____16715 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____16715
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____16723 =
                                                        let uu____16728 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____16728)
                                                         in
                                                      TERM uu____16723  in
                                                    [s1; s2])
                                                  in
                                               let uu____16729 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____16729))))))
                   | uu____16730 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____16801 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____16801
            then
              let uu____16806 = FStar_Syntax_Print.term_to_string t1  in
              let uu____16808 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____16810 = FStar_Syntax_Print.term_to_string t2  in
              let uu____16812 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____16806 uu____16808 uu____16810 uu____16812
            else ());
           (let uu____16823 = FStar_Syntax_Util.head_and_args t1  in
            match uu____16823 with
            | (head1,args1) ->
                let uu____16866 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____16866 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____16936 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____16936 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              k false (defer "universe constraints" orig wl3))
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____16966 =
                         let uu____16968 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____16970 = args_to_string args1  in
                         let uu____16974 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____16976 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____16968 uu____16970 uu____16974 uu____16976
                          in
                       giveup env1 uu____16966 orig
                     else
                       (let uu____16983 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____16992 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____16992 = FStar_Syntax_Util.Equal)
                           in
                        if uu____16983
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___389_16996 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___389_16996.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___389_16996.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___389_16996.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___389_16996.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___389_16996.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___389_16996.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___389_16996.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___389_16996.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17006 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17006
                                    else solve env1 wl2))
                        else
                          (let uu____17011 = base_and_refinement env1 t1  in
                           match uu____17011 with
                           | (base1,refinement1) ->
                               let uu____17036 = base_and_refinement env1 t2
                                  in
                               (match uu____17036 with
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
                                           let uu____17201 =
                                             FStar_List.fold_right
                                               (fun uu____17241  ->
                                                  fun uu____17242  ->
                                                    match (uu____17241,
                                                            uu____17242)
                                                    with
                                                    | (((a1,uu____17294),
                                                        (a2,uu____17296)),
                                                       (probs,wl3)) ->
                                                        let uu____17345 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17345
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17201 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17388 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17388
                                                 then
                                                   let uu____17393 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17393
                                                 else ());
                                                (let uu____17399 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17399
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
                                                    (let uu____17426 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17426 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17442 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17442
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17450 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17450))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____17474 =
                                                    mk_sub_probs wl3  in
                                                  match uu____17474 with
                                                  | (subprobs,wl4) ->
                                                      let wl5 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          [] wl4
                                                         in
                                                      let uu____17488 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____17488)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17514 =
                                           match uu____17514 with
                                           | (prob,reason) ->
                                               ((let uu____17525 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17525
                                                 then
                                                   let uu____17530 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____17532 =
                                                     prob_to_string env2 prob
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____17530 uu____17532
                                                     reason
                                                 else ());
                                                (let uu____17537 =
                                                   let uu____17546 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____17549 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____17546, uu____17549)
                                                    in
                                                 match uu____17537 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____17562 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____17562 with
                                                      | (head1',uu____17580)
                                                          ->
                                                          let uu____17605 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____17605
                                                           with
                                                           | (head2',uu____17623)
                                                               ->
                                                               let uu____17648
                                                                 =
                                                                 let uu____17653
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____17654
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____17653,
                                                                   uu____17654)
                                                                  in
                                                               (match uu____17648
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____17656
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17656
                                                                    then
                                                                    let uu____17661
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____17663
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____17665
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____17667
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17661
                                                                    uu____17663
                                                                    uu____17665
                                                                    uu____17667
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____17672
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___390_17680
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___390_17680.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___390_17680.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___390_17680.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___390_17680.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___390_17680.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___390_17680.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___390_17680.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___390_17680.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____17682
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17682
                                                                    then
                                                                    let uu____17687
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____17687
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____17692 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____17704 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____17704 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____17712 =
                                             let uu____17713 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____17713.FStar_Syntax_Syntax.n
                                              in
                                           match uu____17712 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____17718 -> false  in
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
                                          | uu____17721 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____17724 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___391_17760 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___391_17760.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___391_17760.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___391_17760.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___391_17760.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___391_17760.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___391_17760.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___391_17760.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___391_17760.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____17836 = destruct_flex_t scrutinee wl1  in
             match uu____17836 with
             | ((_t,uv,_args),wl2) ->
                 let uu____17847 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____17847 with
                  | (xs,pat_term,uu____17863,uu____17864) ->
                      let uu____17869 =
                        FStar_List.fold_left
                          (fun uu____17892  ->
                             fun x  ->
                               match uu____17892 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____17913 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____17913 with
                                    | (uu____17932,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____17869 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____17953 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____17953 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___392_17970 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___392_17970.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___392_17970.umax_heuristic_ok);
                                    tcenv = (uu___392_17970.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____17982 = solve env1 wl'  in
                                (match uu____17982 with
                                 | Success (uu____17985,imps) ->
                                     let wl'1 =
                                       let uu___393_17988 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___393_17988.wl_deferred);
                                         ctr = (uu___393_17988.ctr);
                                         defer_ok = (uu___393_17988.defer_ok);
                                         smt_ok = (uu___393_17988.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___393_17988.umax_heuristic_ok);
                                         tcenv = (uu___393_17988.tcenv);
                                         wl_implicits =
                                           (uu___393_17988.wl_implicits)
                                       }  in
                                     let uu____17989 = solve env1 wl'1  in
                                     (match uu____17989 with
                                      | Success (uu____17992,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___394_17996 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___394_17996.attempting);
                                                 wl_deferred =
                                                   (uu___394_17996.wl_deferred);
                                                 ctr = (uu___394_17996.ctr);
                                                 defer_ok =
                                                   (uu___394_17996.defer_ok);
                                                 smt_ok =
                                                   (uu___394_17996.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___394_17996.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___394_17996.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____17997 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18004 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18027 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18027
                 then
                   let uu____18032 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18034 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18032 uu____18034
                 else ());
                (let uu____18039 =
                   let uu____18060 =
                     let uu____18069 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18069)  in
                   let uu____18076 =
                     let uu____18085 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18085)  in
                   (uu____18060, uu____18076)  in
                 match uu____18039 with
                 | ((uu____18115,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18118;
                                   FStar_Syntax_Syntax.vars = uu____18119;_}),
                    (s,t)) ->
                     let uu____18190 =
                       let uu____18192 = is_flex scrutinee  in
                       Prims.op_Negation uu____18192  in
                     if uu____18190
                     then
                       ((let uu____18203 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18203
                         then
                           let uu____18208 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18208
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18227 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18227
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18242 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18242
                           then
                             let uu____18247 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18249 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18247 uu____18249
                           else ());
                          (let pat_discriminates uu___350_18274 =
                             match uu___350_18274 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18290;
                                  FStar_Syntax_Syntax.p = uu____18291;_},FStar_Pervasives_Native.None
                                ,uu____18292) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18306;
                                  FStar_Syntax_Syntax.p = uu____18307;_},FStar_Pervasives_Native.None
                                ,uu____18308) -> true
                             | uu____18335 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18438 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18438 with
                                       | (uu____18440,uu____18441,t') ->
                                           let uu____18459 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18459 with
                                            | (FullMatch ,uu____18471) ->
                                                true
                                            | (HeadMatch
                                               uu____18485,uu____18486) ->
                                                true
                                            | uu____18501 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18538 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18538
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18549 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18549 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18637,uu____18638) ->
                                       branches1
                                   | uu____18783 -> branches  in
                                 let uu____18838 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____18847 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____18847 with
                                        | (p,uu____18851,uu____18852) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_8  -> FStar_Util.Inr _0_8)
                                   uu____18838))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____18910 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____18910 with
                                | (p,uu____18919,e) ->
                                    ((let uu____18938 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____18938
                                      then
                                        let uu____18943 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____18945 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____18943 uu____18945
                                      else ());
                                     (let uu____18950 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _0_9  -> FStar_Util.Inr _0_9)
                                        uu____18950)))))
                 | ((s,t),(uu____18967,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____18970;
                                         FStar_Syntax_Syntax.vars =
                                           uu____18971;_}))
                     ->
                     let uu____19040 =
                       let uu____19042 = is_flex scrutinee  in
                       Prims.op_Negation uu____19042  in
                     if uu____19040
                     then
                       ((let uu____19053 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19053
                         then
                           let uu____19058 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19058
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19077 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19077
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19092 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19092
                           then
                             let uu____19097 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19099 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19097 uu____19099
                           else ());
                          (let pat_discriminates uu___350_19124 =
                             match uu___350_19124 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19140;
                                  FStar_Syntax_Syntax.p = uu____19141;_},FStar_Pervasives_Native.None
                                ,uu____19142) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19156;
                                  FStar_Syntax_Syntax.p = uu____19157;_},FStar_Pervasives_Native.None
                                ,uu____19158) -> true
                             | uu____19185 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19288 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19288 with
                                       | (uu____19290,uu____19291,t') ->
                                           let uu____19309 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19309 with
                                            | (FullMatch ,uu____19321) ->
                                                true
                                            | (HeadMatch
                                               uu____19335,uu____19336) ->
                                                true
                                            | uu____19351 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19388 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19388
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19399 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19399 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19487,uu____19488) ->
                                       branches1
                                   | uu____19633 -> branches  in
                                 let uu____19688 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19697 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19697 with
                                        | (p,uu____19701,uu____19702) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_10  -> FStar_Util.Inr _0_10)
                                   uu____19688))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19760 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19760 with
                                | (p,uu____19769,e) ->
                                    ((let uu____19788 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19788
                                      then
                                        let uu____19793 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19795 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19793 uu____19795
                                      else ());
                                     (let uu____19800 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _0_11  -> FStar_Util.Inr _0_11)
                                        uu____19800)))))
                 | uu____19815 ->
                     ((let uu____19837 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____19837
                       then
                         let uu____19842 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____19844 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____19842 uu____19844
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____19890 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____19890
            then
              let uu____19895 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____19897 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____19899 = FStar_Syntax_Print.term_to_string t1  in
              let uu____19901 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____19895 uu____19897 uu____19899 uu____19901
            else ());
           (let uu____19906 = head_matches_delta env1 wl1 t1 t2  in
            match uu____19906 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____19937,uu____19938) ->
                     let rec may_relate head3 =
                       let uu____19966 =
                         let uu____19967 = FStar_Syntax_Subst.compress head3
                            in
                         uu____19967.FStar_Syntax_Syntax.n  in
                       match uu____19966 with
                       | FStar_Syntax_Syntax.Tm_name uu____19971 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____19973 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____19998 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____19998 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20000 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20003
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20004 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20007,uu____20008) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20050) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20056) ->
                           may_relate t
                       | uu____20061 -> false  in
                     let uu____20063 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20063 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20084 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20084
                          then
                            let uu____20087 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20087 with
                             | (guard,wl2) ->
                                 let uu____20094 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20094)
                          else
                            (let uu____20097 =
                               let uu____20099 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____20101 =
                                 let uu____20103 =
                                   let uu____20107 =
                                     delta_depth_of_term env1 head1  in
                                   FStar_Util.bind_opt uu____20107
                                     (fun x  ->
                                        let uu____20114 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____20114)
                                    in
                                 FStar_Util.dflt "" uu____20103  in
                               let uu____20119 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               let uu____20121 =
                                 let uu____20123 =
                                   let uu____20127 =
                                     delta_depth_of_term env1 head2  in
                                   FStar_Util.bind_opt uu____20127
                                     (fun x  ->
                                        let uu____20134 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____20134)
                                    in
                                 FStar_Util.dflt "" uu____20123  in
                               FStar_Util.format4
                                 "head mismatch (%s (%s) vs %s (%s))"
                                 uu____20099 uu____20101 uu____20119
                                 uu____20121
                                in
                             giveup env1 uu____20097 orig))
                 | (HeadMatch (true ),uu____20140) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20155 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20155 with
                        | (guard,wl2) ->
                            let uu____20162 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20162)
                     else
                       (let uu____20165 =
                          let uu____20167 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____20169 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____20167 uu____20169
                           in
                        giveup env1 uu____20165 orig)
                 | (uu____20172,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___395_20186 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___395_20186.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___395_20186.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___395_20186.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___395_20186.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___395_20186.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___395_20186.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___395_20186.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___395_20186.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20213 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20213
          then
            let uu____20216 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20216
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20222 =
                let uu____20225 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20225  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20222 t1);
             (let uu____20244 =
                let uu____20247 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20247  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20244 t2);
             (let uu____20266 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20266
              then
                let uu____20270 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20272 =
                  let uu____20274 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20276 =
                    let uu____20278 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____20278  in
                  Prims.strcat uu____20274 uu____20276  in
                let uu____20281 =
                  let uu____20283 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20285 =
                    let uu____20287 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____20287  in
                  Prims.strcat uu____20283 uu____20285  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20270 uu____20272 uu____20281
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20294,uu____20295) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20319,FStar_Syntax_Syntax.Tm_delayed uu____20320) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20344,uu____20345) ->
                  let uu____20372 =
                    let uu___396_20373 = problem  in
                    let uu____20374 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___396_20373.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20374;
                      FStar_TypeChecker_Common.relation =
                        (uu___396_20373.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___396_20373.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___396_20373.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___396_20373.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___396_20373.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___396_20373.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___396_20373.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___396_20373.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20372 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20375,uu____20376) ->
                  let uu____20383 =
                    let uu___397_20384 = problem  in
                    let uu____20385 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___397_20384.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20385;
                      FStar_TypeChecker_Common.relation =
                        (uu___397_20384.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___397_20384.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___397_20384.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___397_20384.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___397_20384.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___397_20384.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___397_20384.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___397_20384.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20383 wl
              | (uu____20386,FStar_Syntax_Syntax.Tm_ascribed uu____20387) ->
                  let uu____20414 =
                    let uu___398_20415 = problem  in
                    let uu____20416 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___398_20415.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___398_20415.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___398_20415.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20416;
                      FStar_TypeChecker_Common.element =
                        (uu___398_20415.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___398_20415.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___398_20415.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___398_20415.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___398_20415.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___398_20415.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20414 wl
              | (uu____20417,FStar_Syntax_Syntax.Tm_meta uu____20418) ->
                  let uu____20425 =
                    let uu___399_20426 = problem  in
                    let uu____20427 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___399_20426.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___399_20426.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___399_20426.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20427;
                      FStar_TypeChecker_Common.element =
                        (uu___399_20426.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___399_20426.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___399_20426.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___399_20426.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___399_20426.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___399_20426.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20425 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____20429),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____20431)) ->
                  let uu____20440 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____20440
              | (FStar_Syntax_Syntax.Tm_bvar uu____20441,uu____20442) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____20444,FStar_Syntax_Syntax.Tm_bvar uu____20445) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___351_20515 =
                    match uu___351_20515 with
                    | [] -> c
                    | bs ->
                        let uu____20543 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____20543
                     in
                  let uu____20554 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____20554 with
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
                                    let uu____20703 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____20703
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
                  let mk_t t l uu___352_20792 =
                    match uu___352_20792 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____20834 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____20834 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____20979 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____20980 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____20979
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____20980 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____20982,uu____20983) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21014 -> true
                    | uu____21034 -> false  in
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
                      (let uu____21094 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___400_21102 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___400_21102.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___400_21102.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___400_21102.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___400_21102.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___400_21102.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___400_21102.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___400_21102.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___400_21102.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___400_21102.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___400_21102.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___400_21102.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___400_21102.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___400_21102.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___400_21102.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___400_21102.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___400_21102.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___400_21102.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___400_21102.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___400_21102.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___400_21102.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___400_21102.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___400_21102.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___400_21102.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___400_21102.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___400_21102.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___400_21102.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___400_21102.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___400_21102.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___400_21102.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___400_21102.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___400_21102.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___400_21102.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___400_21102.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___400_21102.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___400_21102.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___400_21102.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___400_21102.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___400_21102.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___400_21102.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___400_21102.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____21094 with
                       | (uu____21107,ty,uu____21109) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21118 =
                                 let uu____21119 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21119.FStar_Syntax_Syntax.n  in
                               match uu____21118 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21122 ->
                                   let uu____21129 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21129
                               | uu____21130 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21133 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21133
                             then
                               let uu____21138 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21140 =
                                 let uu____21142 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21142
                                  in
                               let uu____21143 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21138 uu____21140 uu____21143
                             else ());
                            r1))
                     in
                  let uu____21148 =
                    let uu____21165 = maybe_eta t1  in
                    let uu____21172 = maybe_eta t2  in
                    (uu____21165, uu____21172)  in
                  (match uu____21148 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___401_21214 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___401_21214.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___401_21214.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___401_21214.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___401_21214.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___401_21214.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___401_21214.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___401_21214.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___401_21214.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21235 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21235
                       then
                         let uu____21238 = destruct_flex_t not_abs wl  in
                         (match uu____21238 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___402_21255 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___402_21255.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___402_21255.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___402_21255.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___402_21255.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___402_21255.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___402_21255.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___402_21255.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___402_21255.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21279 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21279
                       then
                         let uu____21282 = destruct_flex_t not_abs wl  in
                         (match uu____21282 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___402_21299 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___402_21299.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___402_21299.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___402_21299.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___402_21299.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___402_21299.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___402_21299.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___402_21299.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___402_21299.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____21303 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21321,FStar_Syntax_Syntax.Tm_abs uu____21322) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21353 -> true
                    | uu____21373 -> false  in
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
                      (let uu____21433 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___400_21441 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___400_21441.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___400_21441.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___400_21441.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___400_21441.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___400_21441.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___400_21441.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___400_21441.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___400_21441.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___400_21441.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___400_21441.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___400_21441.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___400_21441.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___400_21441.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___400_21441.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___400_21441.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___400_21441.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___400_21441.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___400_21441.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___400_21441.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___400_21441.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___400_21441.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___400_21441.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___400_21441.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___400_21441.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___400_21441.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___400_21441.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___400_21441.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___400_21441.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___400_21441.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___400_21441.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___400_21441.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___400_21441.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___400_21441.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___400_21441.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___400_21441.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___400_21441.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___400_21441.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___400_21441.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___400_21441.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___400_21441.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____21433 with
                       | (uu____21446,ty,uu____21448) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21457 =
                                 let uu____21458 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21458.FStar_Syntax_Syntax.n  in
                               match uu____21457 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21461 ->
                                   let uu____21468 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21468
                               | uu____21469 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21472 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21472
                             then
                               let uu____21477 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21479 =
                                 let uu____21481 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21481
                                  in
                               let uu____21482 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21477 uu____21479 uu____21482
                             else ());
                            r1))
                     in
                  let uu____21487 =
                    let uu____21504 = maybe_eta t1  in
                    let uu____21511 = maybe_eta t2  in
                    (uu____21504, uu____21511)  in
                  (match uu____21487 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___401_21553 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___401_21553.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___401_21553.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___401_21553.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___401_21553.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___401_21553.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___401_21553.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___401_21553.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___401_21553.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21574 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21574
                       then
                         let uu____21577 = destruct_flex_t not_abs wl  in
                         (match uu____21577 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___402_21594 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___402_21594.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___402_21594.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___402_21594.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___402_21594.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___402_21594.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___402_21594.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___402_21594.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___402_21594.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21618 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21618
                       then
                         let uu____21621 = destruct_flex_t not_abs wl  in
                         (match uu____21621 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___402_21638 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___402_21638.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___402_21638.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___402_21638.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___402_21638.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___402_21638.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___402_21638.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___402_21638.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___402_21638.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____21642 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____21672 =
                    let uu____21677 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____21677 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___403_21705 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___403_21705.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___403_21705.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___404_21707 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___404_21707.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___404_21707.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____21708,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___403_21723 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___403_21723.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___403_21723.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___404_21725 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___404_21725.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___404_21725.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____21726 -> (x1, x2)  in
                  (match uu____21672 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____21745 = as_refinement false env t11  in
                       (match uu____21745 with
                        | (x12,phi11) ->
                            let uu____21753 = as_refinement false env t21  in
                            (match uu____21753 with
                             | (x22,phi21) ->
                                 ((let uu____21762 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21762
                                   then
                                     ((let uu____21767 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____21769 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21771 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____21767
                                         uu____21769 uu____21771);
                                      (let uu____21774 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____21776 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21778 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____21774
                                         uu____21776 uu____21778))
                                   else ());
                                  (let uu____21783 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____21783 with
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
                                         let uu____21854 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____21854
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____21866 =
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
                                         (let uu____21879 =
                                            let uu____21882 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____21882
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____21879
                                            (p_guard base_prob));
                                         (let uu____21901 =
                                            let uu____21904 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____21904
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____21901
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____21923 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____21923)
                                          in
                                       let has_uvars =
                                         (let uu____21928 =
                                            let uu____21930 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____21930
                                             in
                                          Prims.op_Negation uu____21928) ||
                                           (let uu____21934 =
                                              let uu____21936 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____21936
                                               in
                                            Prims.op_Negation uu____21934)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____21940 =
                                           let uu____21945 =
                                             let uu____21954 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____21954]  in
                                           mk_t_problem wl1 uu____21945 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____21940 with
                                          | (ref_prob,wl2) ->
                                              let uu____21976 =
                                                solve env1
                                                  (let uu___405_21978 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___405_21978.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___405_21978.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___405_21978.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___405_21978.tcenv);
                                                     wl_implicits =
                                                       (uu___405_21978.wl_implicits)
                                                   })
                                                 in
                                              (match uu____21976 with
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
                                               | Success uu____21995 ->
                                                   let guard =
                                                     let uu____22003 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____22003
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___406_22012 = wl3
                                                        in
                                                     {
                                                       attempting =
                                                         (uu___406_22012.attempting);
                                                       wl_deferred =
                                                         (uu___406_22012.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            (Prims.parse_int "1"));
                                                       defer_ok =
                                                         (uu___406_22012.defer_ok);
                                                       smt_ok =
                                                         (uu___406_22012.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___406_22012.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___406_22012.tcenv);
                                                       wl_implicits =
                                                         (uu___406_22012.wl_implicits)
                                                     }  in
                                                   let uu____22014 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____22014))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22017,FStar_Syntax_Syntax.Tm_uvar uu____22018) ->
                  let uu____22043 = destruct_flex_t t1 wl  in
                  (match uu____22043 with
                   | (f1,wl1) ->
                       let uu____22050 = destruct_flex_t t2 wl1  in
                       (match uu____22050 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22057;
                    FStar_Syntax_Syntax.pos = uu____22058;
                    FStar_Syntax_Syntax.vars = uu____22059;_},uu____22060),FStar_Syntax_Syntax.Tm_uvar
                 uu____22061) ->
                  let uu____22110 = destruct_flex_t t1 wl  in
                  (match uu____22110 with
                   | (f1,wl1) ->
                       let uu____22117 = destruct_flex_t t2 wl1  in
                       (match uu____22117 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22124,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22125;
                    FStar_Syntax_Syntax.pos = uu____22126;
                    FStar_Syntax_Syntax.vars = uu____22127;_},uu____22128))
                  ->
                  let uu____22177 = destruct_flex_t t1 wl  in
                  (match uu____22177 with
                   | (f1,wl1) ->
                       let uu____22184 = destruct_flex_t t2 wl1  in
                       (match uu____22184 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22191;
                    FStar_Syntax_Syntax.pos = uu____22192;
                    FStar_Syntax_Syntax.vars = uu____22193;_},uu____22194),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22195;
                    FStar_Syntax_Syntax.pos = uu____22196;
                    FStar_Syntax_Syntax.vars = uu____22197;_},uu____22198))
                  ->
                  let uu____22271 = destruct_flex_t t1 wl  in
                  (match uu____22271 with
                   | (f1,wl1) ->
                       let uu____22278 = destruct_flex_t t2 wl1  in
                       (match uu____22278 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22285,uu____22286) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22299 = destruct_flex_t t1 wl  in
                  (match uu____22299 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22306;
                    FStar_Syntax_Syntax.pos = uu____22307;
                    FStar_Syntax_Syntax.vars = uu____22308;_},uu____22309),uu____22310)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22347 = destruct_flex_t t1 wl  in
                  (match uu____22347 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22354,FStar_Syntax_Syntax.Tm_uvar uu____22355) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22368,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22369;
                    FStar_Syntax_Syntax.pos = uu____22370;
                    FStar_Syntax_Syntax.vars = uu____22371;_},uu____22372))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22409,FStar_Syntax_Syntax.Tm_arrow uu____22410) ->
                  solve_t' env
                    (let uu___407_22438 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___407_22438.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___407_22438.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___407_22438.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___407_22438.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___407_22438.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___407_22438.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___407_22438.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___407_22438.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___407_22438.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22439;
                    FStar_Syntax_Syntax.pos = uu____22440;
                    FStar_Syntax_Syntax.vars = uu____22441;_},uu____22442),FStar_Syntax_Syntax.Tm_arrow
                 uu____22443) ->
                  solve_t' env
                    (let uu___407_22495 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___407_22495.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___407_22495.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___407_22495.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___407_22495.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___407_22495.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___407_22495.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___407_22495.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___407_22495.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___407_22495.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22496,FStar_Syntax_Syntax.Tm_uvar uu____22497) ->
                  let uu____22510 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22510
              | (uu____22511,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22512;
                    FStar_Syntax_Syntax.pos = uu____22513;
                    FStar_Syntax_Syntax.vars = uu____22514;_},uu____22515))
                  ->
                  let uu____22552 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22552
              | (FStar_Syntax_Syntax.Tm_uvar uu____22553,uu____22554) ->
                  let uu____22567 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22567
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22568;
                    FStar_Syntax_Syntax.pos = uu____22569;
                    FStar_Syntax_Syntax.vars = uu____22570;_},uu____22571),uu____22572)
                  ->
                  let uu____22609 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22609
              | (FStar_Syntax_Syntax.Tm_refine uu____22610,uu____22611) ->
                  let t21 =
                    let uu____22619 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____22619  in
                  solve_t env
                    (let uu___408_22645 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___408_22645.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___408_22645.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___408_22645.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___408_22645.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___408_22645.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___408_22645.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___408_22645.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___408_22645.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___408_22645.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22646,FStar_Syntax_Syntax.Tm_refine uu____22647) ->
                  let t11 =
                    let uu____22655 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22655  in
                  solve_t env
                    (let uu___409_22681 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___409_22681.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___409_22681.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___409_22681.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___409_22681.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___409_22681.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___409_22681.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___409_22681.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___409_22681.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___409_22681.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____22763 =
                    let uu____22764 = guard_of_prob env wl problem t1 t2  in
                    match uu____22764 with
                    | (guard,wl1) ->
                        let uu____22771 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____22771
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____22990 = br1  in
                        (match uu____22990 with
                         | (p1,w1,uu____23019) ->
                             let uu____23036 = br2  in
                             (match uu____23036 with
                              | (p2,w2,uu____23059) ->
                                  let uu____23064 =
                                    let uu____23066 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23066  in
                                  if uu____23064
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23093 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23093 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23130 = br2  in
                                         (match uu____23130 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23163 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23163
                                                 in
                                              let uu____23168 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23199,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23220) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23279 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23279 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23168
                                                (fun uu____23351  ->
                                                   match uu____23351 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23388 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23388
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____23409
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____23409
                                                              then
                                                                let uu____23414
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____23416
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____23414
                                                                  uu____23416
                                                              else ());
                                                             (let uu____23422
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____23422
                                                                (fun
                                                                   uu____23458
                                                                    ->
                                                                   match uu____23458
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
                    | uu____23587 -> FStar_Pervasives_Native.None  in
                  let uu____23628 = solve_branches wl brs1 brs2  in
                  (match uu____23628 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____23679 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____23679 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____23713 =
                                FStar_List.map
                                  (fun uu____23725  ->
                                     match uu____23725 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____23713  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____23734 =
                              let uu____23735 =
                                let uu____23736 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____23736
                                  (let uu___410_23744 = wl3  in
                                   {
                                     attempting = (uu___410_23744.attempting);
                                     wl_deferred =
                                       (uu___410_23744.wl_deferred);
                                     ctr = (uu___410_23744.ctr);
                                     defer_ok = (uu___410_23744.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___410_23744.umax_heuristic_ok);
                                     tcenv = (uu___410_23744.tcenv);
                                     wl_implicits =
                                       (uu___410_23744.wl_implicits)
                                   })
                                 in
                              solve env uu____23735  in
                            (match uu____23734 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____23749 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____23756,uu____23757) ->
                  let head1 =
                    let uu____23781 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23781
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23827 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23827
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23873 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23873
                    then
                      let uu____23877 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23879 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23881 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23877 uu____23879 uu____23881
                    else ());
                   (let no_free_uvars t =
                      (let uu____23895 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23895) &&
                        (let uu____23899 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23899)
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
                      let uu____23916 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23916 = FStar_Syntax_Util.Equal  in
                    let uu____23917 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23917
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23921 = equal t1 t2  in
                         (if uu____23921
                          then
                            let uu____23924 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____23924
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23929 =
                            let uu____23936 = equal t1 t2  in
                            if uu____23936
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23949 = mk_eq2 wl env orig t1 t2  in
                               match uu____23949 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____23929 with
                          | (guard,wl1) ->
                              let uu____23970 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____23970))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____23973,uu____23974) ->
                  let head1 =
                    let uu____23982 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23982
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24028 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24028
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24074 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24074
                    then
                      let uu____24078 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24080 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24082 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24078 uu____24080 uu____24082
                    else ());
                   (let no_free_uvars t =
                      (let uu____24096 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24096) &&
                        (let uu____24100 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24100)
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
                      let uu____24117 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24117 = FStar_Syntax_Util.Equal  in
                    let uu____24118 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24118
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24122 = equal t1 t2  in
                         (if uu____24122
                          then
                            let uu____24125 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24125
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24130 =
                            let uu____24137 = equal t1 t2  in
                            if uu____24137
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24150 = mk_eq2 wl env orig t1 t2  in
                               match uu____24150 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24130 with
                          | (guard,wl1) ->
                              let uu____24171 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24171))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24174,uu____24175) ->
                  let head1 =
                    let uu____24177 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24177
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24223 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24223
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24269 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24269
                    then
                      let uu____24273 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24275 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24277 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24273 uu____24275 uu____24277
                    else ());
                   (let no_free_uvars t =
                      (let uu____24291 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24291) &&
                        (let uu____24295 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24295)
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
                      let uu____24312 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24312 = FStar_Syntax_Util.Equal  in
                    let uu____24313 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24313
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24317 = equal t1 t2  in
                         (if uu____24317
                          then
                            let uu____24320 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24320
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24325 =
                            let uu____24332 = equal t1 t2  in
                            if uu____24332
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24345 = mk_eq2 wl env orig t1 t2  in
                               match uu____24345 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24325 with
                          | (guard,wl1) ->
                              let uu____24366 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24366))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24369,uu____24370) ->
                  let head1 =
                    let uu____24372 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24372
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24418 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24418
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24464 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24464
                    then
                      let uu____24468 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24470 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24472 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24468 uu____24470 uu____24472
                    else ());
                   (let no_free_uvars t =
                      (let uu____24486 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24486) &&
                        (let uu____24490 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24490)
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
                      let uu____24507 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24507 = FStar_Syntax_Util.Equal  in
                    let uu____24508 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24508
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24512 = equal t1 t2  in
                         (if uu____24512
                          then
                            let uu____24515 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24515
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24520 =
                            let uu____24527 = equal t1 t2  in
                            if uu____24527
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24540 = mk_eq2 wl env orig t1 t2  in
                               match uu____24540 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24520 with
                          | (guard,wl1) ->
                              let uu____24561 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24561))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____24564,uu____24565) ->
                  let head1 =
                    let uu____24567 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24567
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24613 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24613
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24659 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24659
                    then
                      let uu____24663 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24665 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24667 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24663 uu____24665 uu____24667
                    else ());
                   (let no_free_uvars t =
                      (let uu____24681 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24681) &&
                        (let uu____24685 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24685)
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
                      let uu____24702 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24702 = FStar_Syntax_Util.Equal  in
                    let uu____24703 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24703
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24707 = equal t1 t2  in
                         (if uu____24707
                          then
                            let uu____24710 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24710
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24715 =
                            let uu____24722 = equal t1 t2  in
                            if uu____24722
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24735 = mk_eq2 wl env orig t1 t2  in
                               match uu____24735 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24715 with
                          | (guard,wl1) ->
                              let uu____24756 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24756))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____24759,uu____24760) ->
                  let head1 =
                    let uu____24778 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24778
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24824 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24824
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24870 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24870
                    then
                      let uu____24874 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24876 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24878 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24874 uu____24876 uu____24878
                    else ());
                   (let no_free_uvars t =
                      (let uu____24892 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24892) &&
                        (let uu____24896 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24896)
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
                      let uu____24913 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24913 = FStar_Syntax_Util.Equal  in
                    let uu____24914 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24914
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24918 = equal t1 t2  in
                         (if uu____24918
                          then
                            let uu____24921 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24921
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24926 =
                            let uu____24933 = equal t1 t2  in
                            if uu____24933
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24946 = mk_eq2 wl env orig t1 t2  in
                               match uu____24946 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24926 with
                          | (guard,wl1) ->
                              let uu____24967 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24967))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24970,FStar_Syntax_Syntax.Tm_match uu____24971) ->
                  let head1 =
                    let uu____24995 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24995
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25041 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25041
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25087 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25087
                    then
                      let uu____25091 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25093 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25095 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25091 uu____25093 uu____25095
                    else ());
                   (let no_free_uvars t =
                      (let uu____25109 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25109) &&
                        (let uu____25113 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25113)
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
                      let uu____25130 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25130 = FStar_Syntax_Util.Equal  in
                    let uu____25131 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25131
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25135 = equal t1 t2  in
                         (if uu____25135
                          then
                            let uu____25138 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25138
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25143 =
                            let uu____25150 = equal t1 t2  in
                            if uu____25150
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25163 = mk_eq2 wl env orig t1 t2  in
                               match uu____25163 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25143 with
                          | (guard,wl1) ->
                              let uu____25184 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25184))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25187,FStar_Syntax_Syntax.Tm_uinst uu____25188) ->
                  let head1 =
                    let uu____25196 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25196
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25236 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25236
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25276 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25276
                    then
                      let uu____25280 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25282 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25284 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25280 uu____25282 uu____25284
                    else ());
                   (let no_free_uvars t =
                      (let uu____25298 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25298) &&
                        (let uu____25302 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25302)
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
                      let uu____25319 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25319 = FStar_Syntax_Util.Equal  in
                    let uu____25320 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25320
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25324 = equal t1 t2  in
                         (if uu____25324
                          then
                            let uu____25327 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25327
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25332 =
                            let uu____25339 = equal t1 t2  in
                            if uu____25339
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25352 = mk_eq2 wl env orig t1 t2  in
                               match uu____25352 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25332 with
                          | (guard,wl1) ->
                              let uu____25373 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25373))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25376,FStar_Syntax_Syntax.Tm_name uu____25377) ->
                  let head1 =
                    let uu____25379 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25379
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25419 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25419
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25459 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25459
                    then
                      let uu____25463 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25465 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25467 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25463 uu____25465 uu____25467
                    else ());
                   (let no_free_uvars t =
                      (let uu____25481 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25481) &&
                        (let uu____25485 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25485)
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
                      let uu____25502 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25502 = FStar_Syntax_Util.Equal  in
                    let uu____25503 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25503
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25507 = equal t1 t2  in
                         (if uu____25507
                          then
                            let uu____25510 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25510
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25515 =
                            let uu____25522 = equal t1 t2  in
                            if uu____25522
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25535 = mk_eq2 wl env orig t1 t2  in
                               match uu____25535 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25515 with
                          | (guard,wl1) ->
                              let uu____25556 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25556))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25559,FStar_Syntax_Syntax.Tm_constant uu____25560) ->
                  let head1 =
                    let uu____25562 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25562
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25602 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25602
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25642 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25642
                    then
                      let uu____25646 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25648 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25650 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25646 uu____25648 uu____25650
                    else ());
                   (let no_free_uvars t =
                      (let uu____25664 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25664) &&
                        (let uu____25668 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25668)
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
                      let uu____25685 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25685 = FStar_Syntax_Util.Equal  in
                    let uu____25686 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25686
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25690 = equal t1 t2  in
                         (if uu____25690
                          then
                            let uu____25693 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25693
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25698 =
                            let uu____25705 = equal t1 t2  in
                            if uu____25705
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25718 = mk_eq2 wl env orig t1 t2  in
                               match uu____25718 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25698 with
                          | (guard,wl1) ->
                              let uu____25739 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25739))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25742,FStar_Syntax_Syntax.Tm_fvar uu____25743) ->
                  let head1 =
                    let uu____25745 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25745
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25785 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25785
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25825 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25825
                    then
                      let uu____25829 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25831 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25833 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25829 uu____25831 uu____25833
                    else ());
                   (let no_free_uvars t =
                      (let uu____25847 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25847) &&
                        (let uu____25851 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25851)
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
                      let uu____25868 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25868 = FStar_Syntax_Util.Equal  in
                    let uu____25869 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25869
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25873 = equal t1 t2  in
                         (if uu____25873
                          then
                            let uu____25876 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25876
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25881 =
                            let uu____25888 = equal t1 t2  in
                            if uu____25888
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25901 = mk_eq2 wl env orig t1 t2  in
                               match uu____25901 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25881 with
                          | (guard,wl1) ->
                              let uu____25922 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25922))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25925,FStar_Syntax_Syntax.Tm_app uu____25926) ->
                  let head1 =
                    let uu____25944 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25944
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25984 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25984
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26024 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26024
                    then
                      let uu____26028 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26030 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26032 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26028 uu____26030 uu____26032
                    else ());
                   (let no_free_uvars t =
                      (let uu____26046 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26046) &&
                        (let uu____26050 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26050)
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
                      let uu____26067 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26067 = FStar_Syntax_Util.Equal  in
                    let uu____26068 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26068
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26072 = equal t1 t2  in
                         (if uu____26072
                          then
                            let uu____26075 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26075
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26080 =
                            let uu____26087 = equal t1 t2  in
                            if uu____26087
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26100 = mk_eq2 wl env orig t1 t2  in
                               match uu____26100 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26080 with
                          | (guard,wl1) ->
                              let uu____26121 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26121))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26124,FStar_Syntax_Syntax.Tm_let uu____26125) ->
                  let uu____26152 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26152
                  then
                    let uu____26155 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26155
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____26159,uu____26160) ->
                  let uu____26174 =
                    let uu____26180 =
                      let uu____26182 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26184 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26186 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26188 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26182 uu____26184 uu____26186 uu____26188
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26180)
                     in
                  FStar_Errors.raise_error uu____26174
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26192,FStar_Syntax_Syntax.Tm_let uu____26193) ->
                  let uu____26207 =
                    let uu____26213 =
                      let uu____26215 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26217 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26219 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26221 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26215 uu____26217 uu____26219 uu____26221
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26213)
                     in
                  FStar_Errors.raise_error uu____26207
                    t1.FStar_Syntax_Syntax.pos
              | uu____26225 -> giveup env "head tag mismatch" orig))))

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
          (let uu____26289 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26289
           then
             let uu____26294 =
               let uu____26296 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26296  in
             let uu____26297 =
               let uu____26299 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26299  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26294 uu____26297
           else ());
          (let uu____26303 =
             let uu____26305 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26305  in
           if uu____26303
           then
             let uu____26308 =
               let uu____26310 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____26312 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____26310 uu____26312
                in
             giveup env uu____26308 orig
           else
             (let uu____26317 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____26317 with
              | (ret_sub_prob,wl1) ->
                  let uu____26325 =
                    FStar_List.fold_right2
                      (fun uu____26362  ->
                         fun uu____26363  ->
                           fun uu____26364  ->
                             match (uu____26362, uu____26363, uu____26364)
                             with
                             | ((a1,uu____26408),(a2,uu____26410),(arg_sub_probs,wl2))
                                 ->
                                 let uu____26443 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____26443 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____26325 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____26473 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____26473  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____26481 = attempt sub_probs wl3  in
                       solve env uu____26481)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____26504 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____26507)::[] -> wp1
              | uu____26532 ->
                  let uu____26543 =
                    let uu____26545 =
                      let uu____26547 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____26547  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____26545
                     in
                  failwith uu____26543
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____26554 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____26554]
              | x -> x  in
            let uu____26556 =
              let uu____26567 =
                let uu____26576 =
                  let uu____26577 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____26577 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____26576  in
              [uu____26567]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____26556;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____26595 = lift_c1 ()  in solve_eq uu____26595 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___353_26604  ->
                       match uu___353_26604 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____26609 -> false))
                in
             let uu____26611 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____26641)::uu____26642,(wp2,uu____26644)::uu____26645)
                   -> (wp1, wp2)
               | uu____26718 ->
                   let uu____26743 =
                     let uu____26749 =
                       let uu____26751 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____26753 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____26751 uu____26753
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____26749)
                      in
                   FStar_Errors.raise_error uu____26743
                     env.FStar_TypeChecker_Env.range
                in
             match uu____26611 with
             | (wpc1,wpc2) ->
                 let uu____26763 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____26763
                 then
                   let uu____26768 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____26768 wl
                 else
                   (let uu____26772 =
                      let uu____26779 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____26779  in
                    match uu____26772 with
                    | (c2_decl,qualifiers) ->
                        let uu____26800 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____26800
                        then
                          let c1_repr =
                            let uu____26807 =
                              let uu____26808 =
                                let uu____26809 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____26809  in
                              let uu____26810 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____26808 uu____26810
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____26807
                             in
                          let c2_repr =
                            let uu____26812 =
                              let uu____26813 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____26814 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____26813 uu____26814
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____26812
                             in
                          let uu____26815 =
                            let uu____26820 =
                              let uu____26822 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____26824 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____26822 uu____26824
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____26820
                             in
                          (match uu____26815 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____26830 = attempt [prob] wl2  in
                               solve env uu____26830)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____26845 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____26845
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____26854 =
                                     let uu____26861 =
                                       let uu____26862 =
                                         let uu____26879 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____26882 =
                                           let uu____26893 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____26902 =
                                             let uu____26913 =
                                               let uu____26922 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____26922
                                                in
                                             [uu____26913]  in
                                           uu____26893 :: uu____26902  in
                                         (uu____26879, uu____26882)  in
                                       FStar_Syntax_Syntax.Tm_app uu____26862
                                        in
                                     FStar_Syntax_Syntax.mk uu____26861  in
                                   uu____26854 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____26974 =
                                    let uu____26981 =
                                      let uu____26982 =
                                        let uu____26999 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____27002 =
                                          let uu____27013 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____27022 =
                                            let uu____27033 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____27042 =
                                              let uu____27053 =
                                                let uu____27062 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____27062
                                                 in
                                              [uu____27053]  in
                                            uu____27033 :: uu____27042  in
                                          uu____27013 :: uu____27022  in
                                        (uu____26999, uu____27002)  in
                                      FStar_Syntax_Syntax.Tm_app uu____26982
                                       in
                                    FStar_Syntax_Syntax.mk uu____26981  in
                                  uu____26974 FStar_Pervasives_Native.None r)
                              in
                           (let uu____27119 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____27119
                            then
                              let uu____27124 =
                                let uu____27126 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____27126
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____27124
                            else ());
                           (let uu____27130 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____27130 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____27139 =
                                    let uu____27142 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_12  ->
                                         FStar_Pervasives_Native.Some _0_12)
                                      uu____27142
                                     in
                                  solve_prob orig uu____27139 [] wl1  in
                                let uu____27145 = attempt [base_prob] wl2  in
                                solve env uu____27145))))
           in
        let uu____27146 = FStar_Util.physical_equality c1 c2  in
        if uu____27146
        then
          let uu____27149 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____27149
        else
          ((let uu____27153 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____27153
            then
              let uu____27158 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____27160 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____27158
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____27160
            else ());
           (let uu____27165 =
              let uu____27174 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____27177 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____27174, uu____27177)  in
            match uu____27165 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____27195),FStar_Syntax_Syntax.Total
                    (t2,uu____27197)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____27214 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____27214 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____27216,FStar_Syntax_Syntax.Total uu____27217) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____27236),FStar_Syntax_Syntax.Total
                    (t2,uu____27238)) ->
                     let uu____27255 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____27255 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____27258),FStar_Syntax_Syntax.GTotal
                    (t2,uu____27260)) ->
                     let uu____27277 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____27277 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____27280),FStar_Syntax_Syntax.GTotal
                    (t2,uu____27282)) ->
                     let uu____27299 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____27299 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____27301,FStar_Syntax_Syntax.Comp uu____27302) ->
                     let uu____27311 =
                       let uu___411_27314 = problem  in
                       let uu____27317 =
                         let uu____27318 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27318
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___411_27314.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____27317;
                         FStar_TypeChecker_Common.relation =
                           (uu___411_27314.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___411_27314.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___411_27314.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___411_27314.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___411_27314.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___411_27314.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___411_27314.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___411_27314.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____27311 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____27319,FStar_Syntax_Syntax.Comp uu____27320) ->
                     let uu____27329 =
                       let uu___411_27332 = problem  in
                       let uu____27335 =
                         let uu____27336 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27336
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___411_27332.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____27335;
                         FStar_TypeChecker_Common.relation =
                           (uu___411_27332.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___411_27332.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___411_27332.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___411_27332.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___411_27332.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___411_27332.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___411_27332.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___411_27332.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____27329 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____27337,FStar_Syntax_Syntax.GTotal uu____27338) ->
                     let uu____27347 =
                       let uu___412_27350 = problem  in
                       let uu____27353 =
                         let uu____27354 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27354
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___412_27350.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___412_27350.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___412_27350.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____27353;
                         FStar_TypeChecker_Common.element =
                           (uu___412_27350.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___412_27350.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___412_27350.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___412_27350.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___412_27350.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___412_27350.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____27347 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____27355,FStar_Syntax_Syntax.Total uu____27356) ->
                     let uu____27365 =
                       let uu___412_27368 = problem  in
                       let uu____27371 =
                         let uu____27372 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27372
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___412_27368.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___412_27368.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___412_27368.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____27371;
                         FStar_TypeChecker_Common.element =
                           (uu___412_27368.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___412_27368.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___412_27368.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___412_27368.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___412_27368.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___412_27368.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____27365 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____27373,FStar_Syntax_Syntax.Comp uu____27374) ->
                     let uu____27375 =
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
                     if uu____27375
                     then
                       let uu____27378 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____27378 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____27385 =
                            let uu____27390 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____27390
                            then (c1_comp, c2_comp)
                            else
                              (let uu____27399 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____27400 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____27399, uu____27400))
                             in
                          match uu____27385 with
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
                           (let uu____27408 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____27408
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____27416 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____27416 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____27419 =
                                  let uu____27421 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____27423 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____27421 uu____27423
                                   in
                                giveup env uu____27419 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____27434 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____27434 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____27484 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____27484 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____27509 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____27540  ->
                match uu____27540 with
                | (u1,u2) ->
                    let uu____27548 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____27550 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____27548 uu____27550))
         in
      FStar_All.pipe_right uu____27509 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____27587,[])) when
          let uu____27614 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____27614 -> "{}"
      | uu____27617 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____27644 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____27644
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____27656 =
              FStar_List.map
                (fun uu____27669  ->
                   match uu____27669 with
                   | (uu____27676,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____27656 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____27687 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____27687 imps
  
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
                  let uu____27744 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____27744
                  then
                    let uu____27752 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____27754 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____27752
                      (rel_to_string rel) uu____27754
                  else "TOP"  in
                let uu____27760 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____27760 with
                | (p,wl1) ->
                    (def_check_prob (Prims.strcat "new_t_problem." reason)
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
              let uu____27820 =
                let uu____27823 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_13  -> FStar_Pervasives_Native.Some _0_13)
                  uu____27823
                 in
              FStar_Syntax_Syntax.new_bv uu____27820 t1  in
            let uu____27826 =
              let uu____27831 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____27831
               in
            match uu____27826 with | (p,wl1) -> (p, x, wl1)
  
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
        let sol = solve env probs  in
        match sol with
        | Success (deferred,implicits) ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some (deferred, implicits))
        | Failed (d,s) ->
            ((let uu____27909 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____27909
              then
                let uu____27916 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____27916
              else ());
             (let result = err (d, s)  in
              FStar_Syntax_Unionfind.rollback tx; result))
  
let (simplify_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____27943 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____27943
            then
              let uu____27948 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____27948
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____27955 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____27955
             then
               let uu____27960 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____27960
             else ());
            (let f2 =
               let uu____27966 =
                 let uu____27967 = FStar_Syntax_Util.unmeta f1  in
                 uu____27967.FStar_Syntax_Syntax.n  in
               match uu____27966 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____27971 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___413_27972 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___413_27972.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___413_27972.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___413_27972.FStar_TypeChecker_Env.implicits)
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
            let uu____28027 =
              let uu____28028 =
                let uu____28029 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_14  -> FStar_TypeChecker_Common.NonTrivial _0_14)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____28029;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____28028  in
            FStar_All.pipe_left
              (fun _0_15  -> FStar_Pervasives_Native.Some _0_15) uu____28027
  
let with_guard_no_simp :
  'Auu____28045 .
    'Auu____28045 ->
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
            let uu____28068 =
              let uu____28069 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_16  -> FStar_TypeChecker_Common.NonTrivial _0_16)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____28069;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____28068
  
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
          (let uu____28102 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____28102
           then
             let uu____28107 = FStar_Syntax_Print.term_to_string t1  in
             let uu____28109 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____28107
               uu____28109
           else ());
          (let uu____28114 =
             let uu____28119 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____28119
              in
           match uu____28114 with
           | (prob,wl) ->
               let g =
                 let uu____28127 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____28137  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____28127  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____28173 = try_teq true env t1 t2  in
        match uu____28173 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____28178 = FStar_TypeChecker_Env.get_range env  in
              let uu____28179 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____28178 uu____28179);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____28187 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____28187
              then
                let uu____28192 = FStar_Syntax_Print.term_to_string t1  in
                let uu____28194 = FStar_Syntax_Print.term_to_string t2  in
                let uu____28196 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____28192
                  uu____28194 uu____28196
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
          let uu____28222 = FStar_TypeChecker_Env.get_range env  in
          let uu____28223 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____28222 uu____28223
  
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
        (let uu____28252 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____28252
         then
           let uu____28257 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____28259 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____28257 uu____28259
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____28270 =
           let uu____28277 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____28277 "sub_comp"
            in
         match uu____28270 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____28290 =
                 solve_and_commit env (singleton wl prob1 true)
                   (fun uu____28301  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob1) uu____28290)))
  
let (solve_universe_inequalities' :
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list *
        (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe)
        Prims.list) -> unit)
  =
  fun tx  ->
    fun env  ->
      fun uu____28348  ->
        match uu____28348 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____28391 =
                 let uu____28397 =
                   let uu____28399 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____28401 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____28399 uu____28401
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____28397)  in
               let uu____28405 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____28391 uu____28405)
               in
            let equiv1 v1 v' =
              let uu____28418 =
                let uu____28423 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____28424 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____28423, uu____28424)  in
              match uu____28418 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____28444 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____28475 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____28475 with
                      | FStar_Syntax_Syntax.U_unif uu____28482 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____28511  ->
                                    match uu____28511 with
                                    | (u,v') ->
                                        let uu____28520 = equiv1 v1 v'  in
                                        if uu____28520
                                        then
                                          let uu____28525 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____28525 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____28546 -> []))
               in
            let uu____28551 =
              let wl =
                let uu___414_28555 = empty_worklist env  in
                {
                  attempting = (uu___414_28555.attempting);
                  wl_deferred = (uu___414_28555.wl_deferred);
                  ctr = (uu___414_28555.ctr);
                  defer_ok = false;
                  smt_ok = (uu___414_28555.smt_ok);
                  umax_heuristic_ok = (uu___414_28555.umax_heuristic_ok);
                  tcenv = (uu___414_28555.tcenv);
                  wl_implicits = (uu___414_28555.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____28574  ->
                      match uu____28574 with
                      | (lb,v1) ->
                          let uu____28581 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____28581 with
                           | USolved wl1 -> ()
                           | uu____28584 -> fail1 lb v1)))
               in
            let rec check_ineq uu____28595 =
              match uu____28595 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____28607) -> true
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
                      uu____28631,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____28633,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____28644) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____28652,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____28661 -> false)
               in
            let uu____28667 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____28684  ->
                      match uu____28684 with
                      | (u,v1) ->
                          let uu____28692 = check_ineq (u, v1)  in
                          if uu____28692
                          then true
                          else
                            ((let uu____28700 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____28700
                              then
                                let uu____28705 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____28707 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____28705
                                  uu____28707
                              else ());
                             false)))
               in
            if uu____28667
            then ()
            else
              ((let uu____28717 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____28717
                then
                  ((let uu____28723 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____28723);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____28735 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____28735))
                else ());
               (let uu____28748 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____28748))
  
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
        let fail1 uu____28822 =
          match uu____28822 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___415_28848 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___415_28848.attempting);
            wl_deferred = (uu___415_28848.wl_deferred);
            ctr = (uu___415_28848.ctr);
            defer_ok;
            smt_ok = (uu___415_28848.smt_ok);
            umax_heuristic_ok = (uu___415_28848.umax_heuristic_ok);
            tcenv = (uu___415_28848.tcenv);
            wl_implicits = (uu___415_28848.wl_implicits)
          }  in
        (let uu____28851 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____28851
         then
           let uu____28856 = FStar_Util.string_of_bool defer_ok  in
           let uu____28858 = wl_to_string wl  in
           let uu____28860 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____28856 uu____28858 uu____28860
         else ());
        (let g1 =
           let uu____28866 = solve_and_commit env wl fail1  in
           match uu____28866 with
           | FStar_Pervasives_Native.Some
               (uu____28873::uu____28874,uu____28875) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___416_28904 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___416_28904.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___416_28904.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____28905 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___417_28914 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___417_28914.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___417_28914.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___417_28914.FStar_TypeChecker_Env.implicits)
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
    let uu____28968 = FStar_ST.op_Bang last_proof_ns  in
    match uu____28968 with
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
            let uu___418_29093 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___418_29093.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___418_29093.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___418_29093.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____29094 =
            let uu____29096 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____29096  in
          if uu____29094
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____29108 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____29109 =
                       let uu____29111 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____29111
                        in
                     FStar_Errors.diag uu____29108 uu____29109)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____29119 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____29120 =
                        let uu____29122 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____29122
                         in
                      FStar_Errors.diag uu____29119 uu____29120)
                   else ();
                   (let uu____29128 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____29128
                      "discharge_guard'" env vc1);
                   (let uu____29130 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____29130 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____29139 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____29140 =
                                let uu____29142 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____29142
                                 in
                              FStar_Errors.diag uu____29139 uu____29140)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____29152 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____29153 =
                                let uu____29155 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____29155
                                 in
                              FStar_Errors.diag uu____29152 uu____29153)
                           else ();
                           (let vcs =
                              let uu____29169 = FStar_Options.use_tactics ()
                                 in
                              if uu____29169
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____29191  ->
                                     (let uu____29193 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____29193);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____29237  ->
                                              match uu____29237 with
                                              | (env1,goal,opts) ->
                                                  let uu____29253 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____29253, opts)))))
                              else
                                (let uu____29256 =
                                   let uu____29263 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____29263)  in
                                 [uu____29256])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____29296  ->
                                    match uu____29296 with
                                    | (env1,goal,opts) ->
                                        let uu____29306 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____29306 with
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
                                                (let uu____29318 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____29319 =
                                                   let uu____29321 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____29323 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____29321 uu____29323
                                                    in
                                                 FStar_Errors.diag
                                                   uu____29318 uu____29319)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____29330 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____29331 =
                                                   let uu____29333 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____29333
                                                    in
                                                 FStar_Errors.diag
                                                   uu____29330 uu____29331)
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
      let uu____29351 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____29351 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____29360 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____29360
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____29374 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____29374 with
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
        let uu____29404 = try_teq false env t1 t2  in
        match uu____29404 with
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
            let uu____29448 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____29448 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____29461 ->
                     let uu____29474 =
                       let uu____29475 = FStar_Syntax_Subst.compress r  in
                       uu____29475.FStar_Syntax_Syntax.n  in
                     (match uu____29474 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____29480) ->
                          unresolved ctx_u'
                      | uu____29497 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____29521 = acc  in
            match uu____29521 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____29540 = hd1  in
                     (match uu____29540 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____29551 = unresolved ctx_u  in
                             if uu____29551
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____29575 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____29575
                                     then
                                       let uu____29579 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____29579
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____29588 = teq_nosmt env1 t tm
                                          in
                                       match uu____29588 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Env.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___419_29598 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___419_29598.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___419_29598.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___419_29598.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___419_29598.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___419_29598.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___419_29598.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___419_29598.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___420_29606 = hd1  in
                                       {
                                         FStar_TypeChecker_Env.imp_reason =
                                           (uu___420_29606.FStar_TypeChecker_Env.imp_reason);
                                         FStar_TypeChecker_Env.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Env.imp_tm =
                                           (uu___420_29606.FStar_TypeChecker_Env.imp_tm);
                                         FStar_TypeChecker_Env.imp_range =
                                           (uu___420_29606.FStar_TypeChecker_Env.imp_range)
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
                                    let uu___421_29617 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___421_29617.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___421_29617.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___421_29617.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___421_29617.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___421_29617.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___421_29617.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___421_29617.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___421_29617.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___421_29617.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___421_29617.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___421_29617.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___421_29617.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___421_29617.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___421_29617.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___421_29617.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___421_29617.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___421_29617.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___421_29617.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___421_29617.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___421_29617.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___421_29617.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___421_29617.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___421_29617.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___421_29617.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___421_29617.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___421_29617.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___421_29617.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___421_29617.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___421_29617.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___421_29617.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___421_29617.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___421_29617.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___421_29617.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___421_29617.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___421_29617.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___421_29617.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___421_29617.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___421_29617.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___421_29617.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___421_29617.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___421_29617.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___421_29617.FStar_TypeChecker_Env.nbe)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___422_29621 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___422_29621.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___422_29621.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___422_29621.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___422_29621.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___422_29621.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___422_29621.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___422_29621.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___422_29621.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___422_29621.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___422_29621.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___422_29621.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___422_29621.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___422_29621.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___422_29621.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___422_29621.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___422_29621.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___422_29621.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___422_29621.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___422_29621.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___422_29621.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___422_29621.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___422_29621.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___422_29621.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___422_29621.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___422_29621.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___422_29621.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___422_29621.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___422_29621.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___422_29621.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___422_29621.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___422_29621.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___422_29621.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___422_29621.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___422_29621.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___422_29621.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___422_29621.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___422_29621.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___422_29621.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___422_29621.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___422_29621.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___422_29621.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___422_29621.FStar_TypeChecker_Env.nbe)
                                      }
                                    else env1  in
                                  (let uu____29626 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____29626
                                   then
                                     let uu____29631 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____29633 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____29635 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____29637 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____29631 uu____29633 uu____29635
                                       reason uu____29637
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___424_29644  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____29651 =
                                             let uu____29661 =
                                               let uu____29669 =
                                                 let uu____29671 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____29673 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____29675 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____29671 uu____29673
                                                   uu____29675
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____29669, r)
                                                in
                                             [uu____29661]  in
                                           FStar_Errors.add_errors
                                             uu____29651);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___425_29695 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___425_29695.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___425_29695.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___425_29695.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____29699 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____29710  ->
                                               let uu____29711 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____29713 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____29715 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____29711 uu____29713
                                                 reason uu____29715)) env2 g2
                                         true
                                        in
                                     match uu____29699 with
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
          let uu___426_29723 = g  in
          let uu____29724 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___426_29723.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___426_29723.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___426_29723.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____29724
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
        let uu____29767 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____29767 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____29768 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____29768
      | imp::uu____29770 ->
          let uu____29773 =
            let uu____29779 =
              let uu____29781 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____29783 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____29781 uu____29783 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____29779)
             in
          FStar_Errors.raise_error uu____29773
            imp.FStar_TypeChecker_Env.imp_range
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____29805 = teq_nosmt env t1 t2  in
        match uu____29805 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___427_29824 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___427_29824.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___427_29824.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___427_29824.FStar_TypeChecker_Env.implicits)
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
        (let uu____29860 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____29860
         then
           let uu____29865 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____29867 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____29865
             uu____29867
         else ());
        (let uu____29872 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____29872 with
         | (prob,x,wl) ->
             let g =
               let uu____29891 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____29902  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____29891  in
             ((let uu____29923 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____29923
               then
                 let uu____29928 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____29930 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____29932 =
                   let uu____29934 = FStar_Util.must g  in
                   guard_to_string env uu____29934  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____29928 uu____29930 uu____29932
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
        let uu____29971 = check_subtyping env t1 t2  in
        match uu____29971 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____29990 =
              let uu____29991 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____29991 g  in
            FStar_Pervasives_Native.Some uu____29990
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____30010 = check_subtyping env t1 t2  in
        match uu____30010 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____30029 =
              let uu____30030 =
                let uu____30031 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____30031]  in
              FStar_TypeChecker_Env.close_guard env uu____30030 g  in
            FStar_Pervasives_Native.Some uu____30029
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____30069 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30069
         then
           let uu____30074 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____30076 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____30074
             uu____30076
         else ());
        (let uu____30081 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____30081 with
         | (prob,x,wl) ->
             let g =
               let uu____30096 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____30107  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30096  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____30131 =
                      let uu____30132 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____30132]  in
                    FStar_TypeChecker_Env.close_guard env uu____30131 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____30173 = subtype_nosmt env t1 t2  in
        match uu____30173 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  