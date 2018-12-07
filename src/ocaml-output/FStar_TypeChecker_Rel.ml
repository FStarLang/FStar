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
  
let (whnf :
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
          FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Env.Beta]
            env t
           in
        FStar_Syntax_Subst.compress uu____2897  in
      FStar_All.pipe_right uu____2896 FStar_Syntax_Util.unlazy_emb
  
let norm_arg :
  'Auu____2905 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____2905) ->
        (FStar_Syntax_Syntax.term * 'Auu____2905)
  =
  fun env  ->
    fun t  ->
      let uu____2928 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2928, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____2980  ->
              match uu____2980 with
              | (x,imp) ->
                  let uu____2999 =
                    let uu___364_3000 = x  in
                    let uu____3001 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___364_3000.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___364_3000.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3001
                    }  in
                  (uu____2999, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3025 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3025
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3029 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3029
        | uu____3032 -> u2  in
      let uu____3033 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3033
  
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
                (let uu____3154 = norm_refinement env t12  in
                 match uu____3154 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3169;
                     FStar_Syntax_Syntax.vars = uu____3170;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3194 =
                       let uu____3196 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3198 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3196 uu____3198
                        in
                     failwith uu____3194)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3214 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3214
          | FStar_Syntax_Syntax.Tm_uinst uu____3215 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3252 =
                   let uu____3253 = FStar_Syntax_Subst.compress t1'  in
                   uu____3253.FStar_Syntax_Syntax.n  in
                 match uu____3252 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3268 -> aux true t1'
                 | uu____3276 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3291 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3322 =
                   let uu____3323 = FStar_Syntax_Subst.compress t1'  in
                   uu____3323.FStar_Syntax_Syntax.n  in
                 match uu____3322 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3338 -> aux true t1'
                 | uu____3346 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3361 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3408 =
                   let uu____3409 = FStar_Syntax_Subst.compress t1'  in
                   uu____3409.FStar_Syntax_Syntax.n  in
                 match uu____3408 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3424 -> aux true t1'
                 | uu____3432 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3447 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3462 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3477 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3492 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3507 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3536 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3569 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3590 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3617 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3645 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3682 ->
              let uu____3689 =
                let uu____3691 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3693 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3691 uu____3693
                 in
              failwith uu____3689
          | FStar_Syntax_Syntax.Tm_ascribed uu____3708 ->
              let uu____3735 =
                let uu____3737 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3739 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3737 uu____3739
                 in
              failwith uu____3735
          | FStar_Syntax_Syntax.Tm_delayed uu____3754 ->
              let uu____3777 =
                let uu____3779 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3781 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3779 uu____3781
                 in
              failwith uu____3777
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3796 =
                let uu____3798 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3800 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3798 uu____3800
                 in
              failwith uu____3796
           in
        let uu____3815 = whnf env t1  in aux false uu____3815
  
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
      let uu____3876 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3876 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____3917 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3917, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____3944 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____3944 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4004  ->
    match uu____4004 with
    | (t_base,refopt) ->
        let uu____4035 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4035 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4077 =
      let uu____4081 =
        let uu____4084 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4111  ->
                  match uu____4111 with | (uu____4120,uu____4121,x) -> x))
           in
        FStar_List.append wl.attempting uu____4084  in
      FStar_List.map (wl_prob_to_string wl) uu____4081  in
    FStar_All.pipe_right uu____4077 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____4144 .
    ('Auu____4144 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____4156  ->
    match uu____4156 with
    | (uu____4163,c,args) ->
        let uu____4166 = print_ctx_uvar c  in
        let uu____4168 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4166 uu____4168
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4178 = FStar_Syntax_Util.head_and_args t  in
    match uu____4178 with
    | (head1,_args) ->
        let uu____4222 =
          let uu____4223 = FStar_Syntax_Subst.compress head1  in
          uu____4223.FStar_Syntax_Syntax.n  in
        (match uu____4222 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4227 -> true
         | uu____4241 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4249 = FStar_Syntax_Util.head_and_args t  in
    match uu____4249 with
    | (head1,_args) ->
        let uu____4292 =
          let uu____4293 = FStar_Syntax_Subst.compress head1  in
          uu____4293.FStar_Syntax_Syntax.n  in
        (match uu____4292 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4297) -> u
         | uu____4314 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____4339 = FStar_Syntax_Util.head_and_args t  in
      match uu____4339 with
      | (head1,args) ->
          let uu____4386 =
            let uu____4387 = FStar_Syntax_Subst.compress head1  in
            uu____4387.FStar_Syntax_Syntax.n  in
          (match uu____4386 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4395)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4428 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___340_4453  ->
                         match uu___340_4453 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4458 =
                               let uu____4459 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4459.FStar_Syntax_Syntax.n  in
                             (match uu____4458 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4464 -> false)
                         | uu____4466 -> true))
                  in
               (match uu____4428 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4491 =
                        FStar_List.collect
                          (fun uu___341_4503  ->
                             match uu___341_4503 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4507 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4507]
                             | uu____4508 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4491 FStar_List.rev  in
                    let uu____4531 =
                      let uu____4538 =
                        let uu____4547 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___342_4569  ->
                                  match uu___342_4569 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4573 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4573]
                                  | uu____4574 -> []))
                           in
                        FStar_All.pipe_right uu____4547 FStar_List.rev  in
                      let uu____4597 =
                        let uu____4600 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4600  in
                      new_uvar
                        (Prims.strcat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4538 uu____4597
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____4531 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4636  ->
                                match uu____4636 with
                                | (x,i) ->
                                    let uu____4655 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4655, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4686  ->
                                match uu____4686 with
                                | (a,i) ->
                                    let uu____4705 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4705, i)) args_sol
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
           | uu____4727 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4749 =
          let uu____4772 =
            let uu____4773 = FStar_Syntax_Subst.compress k  in
            uu____4773.FStar_Syntax_Syntax.n  in
          match uu____4772 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4855 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____4855)
              else
                (let uu____4890 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4890 with
                 | (ys',t1,uu____4923) ->
                     let uu____4928 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____4928))
          | uu____4967 ->
              let uu____4968 =
                let uu____4973 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____4973)  in
              ((ys, t), uu____4968)
           in
        match uu____4749 with
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
                 let uu____5068 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5068 c  in
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
               (let uu____5146 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5146
                then
                  let uu____5151 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5153 = print_ctx_uvar uv  in
                  let uu____5155 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5151 uu____5153 uu____5155
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5164 =
                   let uu____5166 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.strcat "solve_prob'.sol." uu____5166  in
                 let uu____5169 =
                   let uu____5172 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5172
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5164 uu____5169 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____5205 =
               let uu____5206 =
                 let uu____5208 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5210 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5208 uu____5210
                  in
               failwith uu____5206  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5276  ->
                       match uu____5276 with
                       | (a,i) ->
                           let uu____5297 =
                             let uu____5298 = FStar_Syntax_Subst.compress a
                                in
                             uu____5298.FStar_Syntax_Syntax.n  in
                           (match uu____5297 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5324 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____5334 =
                 let uu____5336 = is_flex g  in Prims.op_Negation uu____5336
                  in
               if uu____5334
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____5345 = destruct_flex_t g wl  in
                  match uu____5345 with
                  | ((uu____5350,uv1,args),wl1) ->
                      ((let uu____5355 = args_as_binders args  in
                        assign_solution uu____5355 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___365_5357 = wl1  in
              {
                attempting = (uu___365_5357.attempting);
                wl_deferred = (uu___365_5357.wl_deferred);
                ctr = (wl1.ctr + (Prims.parse_int "1"));
                defer_ok = (uu___365_5357.defer_ok);
                smt_ok = (uu___365_5357.smt_ok);
                umax_heuristic_ok = (uu___365_5357.umax_heuristic_ok);
                tcenv = (uu___365_5357.tcenv);
                wl_implicits = (uu___365_5357.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5382 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5382
         then
           let uu____5387 = FStar_Util.string_of_int pid  in
           let uu____5389 =
             let uu____5391 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____5391 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5387 uu____5389
         else ());
        commit sol;
        (let uu___366_5405 = wl  in
         {
           attempting = (uu___366_5405.attempting);
           wl_deferred = (uu___366_5405.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___366_5405.defer_ok);
           smt_ok = (uu___366_5405.smt_ok);
           umax_heuristic_ok = (uu___366_5405.umax_heuristic_ok);
           tcenv = (uu___366_5405.tcenv);
           wl_implicits = (uu___366_5405.wl_implicits)
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
             | (uu____5471,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____5499 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____5499
              in
           (let uu____5505 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____5505
            then
              let uu____5510 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____5514 =
                let uu____5516 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____5516 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____5510 uu____5514
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
        let uu____5551 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5551 FStar_Util.set_elements  in
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
      let uu____5591 = occurs uk t  in
      match uu____5591 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5630 =
                 let uu____5632 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5634 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5632 uu____5634
                  in
               FStar_Pervasives_Native.Some uu____5630)
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
            let uu____5754 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5754 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5805 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5862  ->
             match uu____5862 with
             | (x,uu____5874) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____5892 = FStar_List.last bs  in
      match uu____5892 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____5916) ->
          let uu____5927 =
            FStar_Util.prefix_until
              (fun uu___343_5942  ->
                 match uu___343_5942 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____5945 -> false) g
             in
          (match uu____5927 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____5959,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____5996 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____5996 with
        | (pfx,uu____6006) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6018 =
              new_uvar
                (Prims.strcat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6018 with
             | (uu____6026,src',wl1) ->
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
                 | uu____6140 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6141 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6205  ->
                  fun uu____6206  ->
                    match (uu____6205, uu____6206) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6309 =
                          let uu____6311 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6311
                           in
                        if uu____6309
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6345 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6345
                           then
                             let uu____6362 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6362)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6141 with | (isect,uu____6412) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____6448 'Auu____6449 .
    (FStar_Syntax_Syntax.bv * 'Auu____6448) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____6449) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6507  ->
              fun uu____6508  ->
                match (uu____6507, uu____6508) with
                | ((a,uu____6527),(b,uu____6529)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____6545 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____6545) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6576  ->
           match uu____6576 with
           | (y,uu____6583) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6593 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____6593) Prims.list ->
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
                   let uu____6755 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6755
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6788 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6840 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____6885 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____6907 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___344_6915  ->
    match uu___344_6915 with
    | MisMatch (d1,d2) ->
        let uu____6927 =
          let uu____6929 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____6931 =
            let uu____6933 =
              let uu____6935 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____6935 ")"  in
            Prims.strcat ") (" uu____6933  in
          Prims.strcat uu____6929 uu____6931  in
        Prims.strcat "MisMatch (" uu____6927
    | HeadMatch u ->
        let uu____6942 = FStar_Util.string_of_bool u  in
        Prims.strcat "HeadMatch " uu____6942
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___345_6951  ->
    match uu___345_6951 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____6968 -> HeadMatch false
  
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
          let uu____6990 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6990 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7001 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7025 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7035 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7062 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7062
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7063 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7064 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7065 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7078 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7092 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7116) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7122,uu____7123) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7165) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7190;
             FStar_Syntax_Syntax.index = uu____7191;
             FStar_Syntax_Syntax.sort = t2;_},uu____7193)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7201 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7202 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7203 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7218 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7225 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7245 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7245
  
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
           { FStar_Syntax_Syntax.blob = uu____7264;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7265;
             FStar_Syntax_Syntax.ltyp = uu____7266;
             FStar_Syntax_Syntax.rng = uu____7267;_},uu____7268)
            ->
            let uu____7279 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7279 t21
        | (uu____7280,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7281;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7282;
             FStar_Syntax_Syntax.ltyp = uu____7283;
             FStar_Syntax_Syntax.rng = uu____7284;_})
            ->
            let uu____7295 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7295
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7307 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7307
            then FullMatch
            else
              (let uu____7312 =
                 let uu____7321 =
                   let uu____7324 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7324  in
                 let uu____7325 =
                   let uu____7328 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7328  in
                 (uu____7321, uu____7325)  in
               MisMatch uu____7312)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7334),FStar_Syntax_Syntax.Tm_uinst (g,uu____7336)) ->
            let uu____7345 = head_matches env f g  in
            FStar_All.pipe_right uu____7345 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7348 = FStar_Const.eq_const c d  in
            if uu____7348
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7358),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7360)) ->
            let uu____7393 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7393
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7403),FStar_Syntax_Syntax.Tm_refine (y,uu____7405)) ->
            let uu____7414 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7414 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____7416),uu____7417) ->
            let uu____7422 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____7422 head_match
        | (uu____7423,FStar_Syntax_Syntax.Tm_refine (x,uu____7425)) ->
            let uu____7430 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7430 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7431,FStar_Syntax_Syntax.Tm_type
           uu____7432) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____7434,FStar_Syntax_Syntax.Tm_arrow uu____7435) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____7466),FStar_Syntax_Syntax.Tm_app (head',uu____7468))
            ->
            let uu____7517 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____7517 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____7519),uu____7520) ->
            let uu____7545 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____7545 head_match
        | (uu____7546,FStar_Syntax_Syntax.Tm_app (head1,uu____7548)) ->
            let uu____7573 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____7573 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7574,FStar_Syntax_Syntax.Tm_let
           uu____7575) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____7603,FStar_Syntax_Syntax.Tm_match uu____7604) ->
            HeadMatch true
        | uu____7650 ->
            let uu____7655 =
              let uu____7664 = delta_depth_of_term env t11  in
              let uu____7667 = delta_depth_of_term env t21  in
              (uu____7664, uu____7667)  in
            MisMatch uu____7655
  
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
            (let uu____7733 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7733
             then
               let uu____7738 = FStar_Syntax_Print.term_to_string t  in
               let uu____7740 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7738 uu____7740
             else ());
            (let uu____7745 =
               let uu____7746 = FStar_Syntax_Util.un_uinst head1  in
               uu____7746.FStar_Syntax_Syntax.n  in
             match uu____7745 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7752 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7752 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7766 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7766
                        then
                          let uu____7771 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7771
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7776 ->
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
                      let uu____7793 =
                        let uu____7795 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____7795 = FStar_Syntax_Util.Equal  in
                      if uu____7793
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____7802 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____7802
                          then
                            let uu____7807 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____7809 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____7807
                              uu____7809
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____7814 -> FStar_Pervasives_Native.None)
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
            (let uu____7966 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7966
             then
               let uu____7971 = FStar_Syntax_Print.term_to_string t11  in
               let uu____7973 = FStar_Syntax_Print.term_to_string t21  in
               let uu____7975 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____7971
                 uu____7973 uu____7975
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8003 =
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
               match uu____8003 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____8051 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8051 with
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
                  uu____8089),uu____8090)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8111 =
                      let uu____8120 = maybe_inline t11  in
                      let uu____8123 = maybe_inline t21  in
                      (uu____8120, uu____8123)  in
                    match uu____8111 with
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
                 (uu____8166,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8167))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8188 =
                      let uu____8197 = maybe_inline t11  in
                      let uu____8200 = maybe_inline t21  in
                      (uu____8197, uu____8200)  in
                    match uu____8188 with
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
             | MisMatch uu____8255 -> fail1 n_delta r t11 t21
             | uu____8264 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____8279 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8279
           then
             let uu____8284 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8286 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8288 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8296 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8313 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8313
                    (fun uu____8348  ->
                       match uu____8348 with
                       | (t11,t21) ->
                           let uu____8356 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8358 =
                             let uu____8360 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.strcat "; " uu____8360  in
                           Prims.strcat uu____8356 uu____8358))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8284 uu____8286 uu____8288 uu____8296
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____8377 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____8377 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___346_8392  ->
    match uu___346_8392 with
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
      let uu___367_8441 = p  in
      let uu____8444 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8445 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___367_8441.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8444;
        FStar_TypeChecker_Common.relation =
          (uu___367_8441.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8445;
        FStar_TypeChecker_Common.element =
          (uu___367_8441.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___367_8441.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___367_8441.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___367_8441.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___367_8441.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___367_8441.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8460 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____8460
            (fun _0_5  -> FStar_TypeChecker_Common.TProb _0_5)
      | FStar_TypeChecker_Common.CProb uu____8465 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____8488 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____8488 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8496 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8496 with
           | (lh,lhs_args) ->
               let uu____8543 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8543 with
                | (rh,rhs_args) ->
                    let uu____8590 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8603,FStar_Syntax_Syntax.Tm_uvar uu____8604)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8693 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8720,uu____8721)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8736,FStar_Syntax_Syntax.Tm_uvar uu____8737)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8752,FStar_Syntax_Syntax.Tm_arrow uu____8753)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___368_8783 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___368_8783.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___368_8783.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___368_8783.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___368_8783.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___368_8783.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___368_8783.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___368_8783.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___368_8783.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___368_8783.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8786,FStar_Syntax_Syntax.Tm_type uu____8787)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___368_8803 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___368_8803.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___368_8803.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___368_8803.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___368_8803.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___368_8803.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___368_8803.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___368_8803.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___368_8803.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___368_8803.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____8806,FStar_Syntax_Syntax.Tm_uvar uu____8807)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___368_8823 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___368_8823.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___368_8823.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___368_8823.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___368_8823.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___368_8823.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___368_8823.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___368_8823.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___368_8823.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___368_8823.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____8826,FStar_Syntax_Syntax.Tm_uvar uu____8827)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8842,uu____8843)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8858,FStar_Syntax_Syntax.Tm_uvar uu____8859)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8874,uu____8875) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____8590 with
                     | (rank,tp1) ->
                         let uu____8888 =
                           FStar_All.pipe_right
                             (let uu___369_8892 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___369_8892.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___369_8892.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___369_8892.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___369_8892.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___369_8892.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___369_8892.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___369_8892.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___369_8892.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___369_8892.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_6  ->
                                FStar_TypeChecker_Common.TProb _0_6)
                            in
                         (rank, uu____8888))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8898 =
            FStar_All.pipe_right
              (let uu___370_8902 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___370_8902.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___370_8902.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___370_8902.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___370_8902.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___370_8902.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___370_8902.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___370_8902.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___370_8902.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___370_8902.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_7  -> FStar_TypeChecker_Common.CProb _0_7)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____8898)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____8964 probs =
      match uu____8964 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9045 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____9066 = rank wl.tcenv hd1  in
               (match uu____9066 with
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
                      (let uu____9127 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9132 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9132)
                          in
                       if uu____9127
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
          let uu____9205 = FStar_Syntax_Util.head_and_args t  in
          match uu____9205 with
          | (hd1,uu____9224) ->
              let uu____9249 =
                let uu____9250 = FStar_Syntax_Subst.compress hd1  in
                uu____9250.FStar_Syntax_Syntax.n  in
              (match uu____9249 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9255) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9290  ->
                           match uu____9290 with
                           | (y,uu____9299) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9322  ->
                                       match uu____9322 with
                                       | (x,uu____9331) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9336 -> false)
           in
        let uu____9338 = rank tcenv p  in
        match uu____9338 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9347 -> true
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
    match projectee with | UDeferred _0 -> true | uu____9384 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9404 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9425 -> false
  
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
                        let uu____9488 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9488 with
                        | (k,uu____9496) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9509 -> false)))
            | uu____9511 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9563 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9571 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9571 = (Prims.parse_int "0")))
                           in
                        if uu____9563 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9592 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9600 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9600 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____9592)
               in
            let uu____9604 = filter1 u12  in
            let uu____9607 = filter1 u22  in (uu____9604, uu____9607)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then UFailed "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9642 = filter_out_common_univs us1 us2  in
                   (match uu____9642 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____9702 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____9702 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9705 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          (let uu____9716 =
                             let uu____9718 =
                               FStar_Syntax_Print.univ_to_string u12  in
                             let uu____9720 =
                               FStar_Syntax_Print.univ_to_string u22  in
                             FStar_Util.format2
                               "Unable to unify universes: %s and %s"
                               uu____9718 uu____9720
                              in
                           UFailed uu____9716))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9746 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____9746 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9772 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____9772 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____9775 ->
                   let uu____9780 =
                     let uu____9782 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____9784 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format3
                       "Unable to unify universes: %s and %s (%s)" uu____9782
                       uu____9784 msg
                      in
                   UFailed uu____9780)
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9787,uu____9788) ->
              let uu____9790 =
                let uu____9792 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9794 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9792 uu____9794
                 in
              failwith uu____9790
          | (FStar_Syntax_Syntax.U_unknown ,uu____9797) ->
              let uu____9798 =
                let uu____9800 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9802 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9800 uu____9802
                 in
              failwith uu____9798
          | (uu____9805,FStar_Syntax_Syntax.U_bvar uu____9806) ->
              let uu____9808 =
                let uu____9810 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9812 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9810 uu____9812
                 in
              failwith uu____9808
          | (uu____9815,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9816 =
                let uu____9818 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9820 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9818 uu____9820
                 in
              failwith uu____9816
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9850 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____9850
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____9867 = occurs_univ v1 u3  in
              if uu____9867
              then
                let uu____9870 =
                  let uu____9872 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9874 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9872 uu____9874
                   in
                try_umax_components u11 u21 uu____9870
              else
                (let uu____9879 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9879)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____9891 = occurs_univ v1 u3  in
              if uu____9891
              then
                let uu____9894 =
                  let uu____9896 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9898 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9896 uu____9898
                   in
                try_umax_components u11 u21 uu____9894
              else
                (let uu____9903 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9903)
          | (FStar_Syntax_Syntax.U_max uu____9904,uu____9905) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9913 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9913
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9919,FStar_Syntax_Syntax.U_max uu____9920) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9928 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9928
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9934,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9936,FStar_Syntax_Syntax.U_name
             uu____9937) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9939) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9941) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9943,FStar_Syntax_Syntax.U_succ
             uu____9944) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9946,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
  
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
      let uu____10053 = bc1  in
      match uu____10053 with
      | (bs1,mk_cod1) ->
          let uu____10097 = bc2  in
          (match uu____10097 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10208 = aux xs ys  in
                     (match uu____10208 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10291 =
                       let uu____10298 = mk_cod1 xs  in ([], uu____10298)  in
                     let uu____10301 =
                       let uu____10308 = mk_cod2 ys  in ([], uu____10308)  in
                     (uu____10291, uu____10301)
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
                  let uu____10377 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10377 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____10380 =
                    let uu____10381 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____10381 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____10380
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____10386 = has_type_guard t1 t2  in (uu____10386, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____10387 = has_type_guard t2 t1  in (uu____10387, wl)
  
let is_flex_pat :
  'Auu____10397 'Auu____10398 'Auu____10399 .
    ('Auu____10397 * 'Auu____10398 * 'Auu____10399 Prims.list) -> Prims.bool
  =
  fun uu___347_10413  ->
    match uu___347_10413 with
    | (uu____10422,uu____10423,[]) -> true
    | uu____10427 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____10460 = f  in
      match uu____10460 with
      | (uu____10467,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____10468;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10469;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____10472;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____10473;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____10474;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____10475;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10545  ->
                 match uu____10545 with
                 | (y,uu____10554) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____10708 =
                  let uu____10723 =
                    let uu____10726 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____10726  in
                  ((FStar_List.rev pat_binders), uu____10723)  in
                FStar_Pervasives_Native.Some uu____10708
            | (uu____10759,[]) ->
                let uu____10790 =
                  let uu____10805 =
                    let uu____10808 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____10808  in
                  ((FStar_List.rev pat_binders), uu____10805)  in
                FStar_Pervasives_Native.Some uu____10790
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____10899 =
                  let uu____10900 = FStar_Syntax_Subst.compress a  in
                  uu____10900.FStar_Syntax_Syntax.n  in
                (match uu____10899 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____10920 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____10920
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___371_10950 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___371_10950.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___371_10950.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____10954 =
                            let uu____10955 =
                              let uu____10962 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____10962)  in
                            FStar_Syntax_Syntax.NT uu____10955  in
                          [uu____10954]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___372_10978 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___372_10978.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___372_10978.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____10979 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11019 =
                  let uu____11034 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11034  in
                (match uu____11019 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11109 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11142 ->
               let uu____11143 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11143 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____11465 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____11465
       then
         let uu____11470 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11470
       else ());
      (let uu____11475 = next_prob probs  in
       match uu____11475 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___373_11502 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___373_11502.wl_deferred);
               ctr = (uu___373_11502.ctr);
               defer_ok = (uu___373_11502.defer_ok);
               smt_ok = (uu___373_11502.smt_ok);
               umax_heuristic_ok = (uu___373_11502.umax_heuristic_ok);
               tcenv = (uu___373_11502.tcenv);
               wl_implicits = (uu___373_11502.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11511 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____11511
                 then
                   let uu____11514 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____11514
                 else
                   if
                     (rank1 = FStar_TypeChecker_Common.Rigid_rigid) ||
                       ((tp.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                          && (rank1 <> FStar_TypeChecker_Common.Flex_flex))
                   then solve_t' env tp probs1
                   else
                     if probs1.defer_ok
                     then
                       solve env
                         (defer "deferring flex_rigid or flex_flex subtyping"
                            hd1 probs1)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t' env
                           (let uu___374_11526 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___374_11526.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___374_11526.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___374_11526.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___374_11526.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___374_11526.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___374_11526.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___374_11526.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___374_11526.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___374_11526.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____11552 ->
                let uu____11563 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11634  ->
                          match uu____11634 with
                          | (c,uu____11645,uu____11646) -> c < probs.ctr))
                   in
                (match uu____11563 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11701 =
                            let uu____11706 =
                              FStar_List.map
                                (fun uu____11724  ->
                                   match uu____11724 with
                                   | (uu____11738,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____11706, (probs.wl_implicits))  in
                          Success uu____11701
                      | uu____11746 ->
                          let uu____11757 =
                            let uu___375_11758 = probs  in
                            let uu____11759 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____11782  ->
                                      match uu____11782 with
                                      | (uu____11791,uu____11792,y) -> y))
                               in
                            {
                              attempting = uu____11759;
                              wl_deferred = rest;
                              ctr = (uu___375_11758.ctr);
                              defer_ok = (uu___375_11758.defer_ok);
                              smt_ok = (uu___375_11758.smt_ok);
                              umax_heuristic_ok =
                                (uu___375_11758.umax_heuristic_ok);
                              tcenv = (uu___375_11758.tcenv);
                              wl_implicits = (uu___375_11758.wl_implicits)
                            }  in
                          solve env uu____11757))))

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
            let uu____11803 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____11803 with
            | USolved wl1 ->
                let uu____11805 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____11805
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
                  let uu____11859 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____11859 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____11862 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____11875;
                  FStar_Syntax_Syntax.vars = uu____11876;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____11879;
                  FStar_Syntax_Syntax.vars = uu____11880;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____11893,uu____11894) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____11902,FStar_Syntax_Syntax.Tm_uinst uu____11903) ->
                failwith "Impossible: expect head symbols to match"
            | uu____11911 -> USolved wl

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
            ((let uu____11923 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____11923
              then
                let uu____11928 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____11928 msg
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
               let uu____12020 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12020 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12075 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12075
                then
                  let uu____12080 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12082 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12080 uu____12082
                else ());
               (let uu____12087 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12087 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12133 = eq_prob t1 t2 wl2  in
                         (match uu____12133 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12154 ->
                         let uu____12163 = eq_prob t1 t2 wl2  in
                         (match uu____12163 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____12213 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____12228 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____12229 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____12228, uu____12229)
                           | FStar_Pervasives_Native.None  ->
                               let uu____12234 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____12235 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____12234, uu____12235)
                            in
                         (match uu____12213 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12266 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____12266 with
                                | (t1_hd,t1_args) ->
                                    let uu____12311 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____12311 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12377 =
                                              let uu____12384 =
                                                let uu____12395 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____12395 :: t1_args  in
                                              let uu____12412 =
                                                let uu____12421 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____12421 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____12470  ->
                                                   fun uu____12471  ->
                                                     fun uu____12472  ->
                                                       match (uu____12470,
                                                               uu____12471,
                                                               uu____12472)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____12522),
                                                          (a2,uu____12524))
                                                           ->
                                                           let uu____12561 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____12561
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12384
                                                uu____12412
                                               in
                                            match uu____12377 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___376_12587 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___376_12587.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___376_12587.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___376_12587.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12599 =
                                                  solve env1 wl'  in
                                                (match uu____12599 with
                                                 | Success (uu____12602,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___377_12606
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___377_12606.attempting);
                                                            wl_deferred =
                                                              (uu___377_12606.wl_deferred);
                                                            ctr =
                                                              (uu___377_12606.ctr);
                                                            defer_ok =
                                                              (uu___377_12606.defer_ok);
                                                            smt_ok =
                                                              (uu___377_12606.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___377_12606.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___377_12606.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____12607 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____12640 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____12640 with
                                | (t1_base,p1_opt) ->
                                    let uu____12676 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____12676 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____12775 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____12775
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
                                               let uu____12828 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____12828
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
                                               let uu____12860 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____12860
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
                                               let uu____12892 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____12892
                                           | uu____12895 -> t_base  in
                                         let uu____12912 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____12912 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____12926 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____12926, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____12933 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____12933 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____12969 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____12969 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13005 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13005
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
                              let uu____13029 = combine t11 t21 wl2  in
                              (match uu____13029 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13062 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13062
                                     then
                                       let uu____13067 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13067
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13109 ts1 =
               match uu____13109 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13172 = pairwise out t wl2  in
                        (match uu____13172 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____13208 =
               let uu____13219 = FStar_List.hd ts  in (uu____13219, [], wl1)
                in
             let uu____13228 = FStar_List.tl ts  in
             aux uu____13208 uu____13228  in
           let uu____13235 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____13235 with
           | (this_flex,this_rigid) ->
               let uu____13261 =
                 let uu____13262 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____13262.FStar_Syntax_Syntax.n  in
               (match uu____13261 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____13287 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____13287
                    then
                      let uu____13290 = destruct_flex_t this_flex wl  in
                      (match uu____13290 with
                       | (flex,wl1) ->
                           let uu____13297 = quasi_pattern env flex  in
                           (match uu____13297 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____13316 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____13316
                                  then
                                    let uu____13321 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13321
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13328 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___378_13331 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___378_13331.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___378_13331.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___378_13331.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___378_13331.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___378_13331.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___378_13331.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___378_13331.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___378_13331.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___378_13331.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____13328)
                | uu____13332 ->
                    ((let uu____13334 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13334
                      then
                        let uu____13339 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13339
                      else ());
                     (let uu____13344 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____13344 with
                      | (u,_args) ->
                          let uu____13387 =
                            let uu____13388 = FStar_Syntax_Subst.compress u
                               in
                            uu____13388.FStar_Syntax_Syntax.n  in
                          (match uu____13387 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____13416 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____13416 with
                                 | (u',uu____13435) ->
                                     let uu____13460 =
                                       let uu____13461 = whnf env u'  in
                                       uu____13461.FStar_Syntax_Syntax.n  in
                                     (match uu____13460 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13483 -> false)
                                  in
                               let uu____13485 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___348_13508  ->
                                         match uu___348_13508 with
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
                                              | uu____13522 -> false)
                                         | uu____13526 -> false))
                                  in
                               (match uu____13485 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____13541 = whnf env this_rigid
                                         in
                                      let uu____13542 =
                                        FStar_List.collect
                                          (fun uu___349_13548  ->
                                             match uu___349_13548 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13554 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____13554]
                                             | uu____13558 -> [])
                                          bounds_probs
                                         in
                                      uu____13541 :: uu____13542  in
                                    let uu____13559 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____13559 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____13592 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____13607 =
                                               let uu____13608 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____13608.FStar_Syntax_Syntax.n
                                                in
                                             match uu____13607 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13620 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13620)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13631 -> bound  in
                                           let uu____13632 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____13632)  in
                                         (match uu____13592 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13667 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____13667
                                                then
                                                  let wl'1 =
                                                    let uu___379_13673 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___379_13673.wl_deferred);
                                                      ctr =
                                                        (uu___379_13673.ctr);
                                                      defer_ok =
                                                        (uu___379_13673.defer_ok);
                                                      smt_ok =
                                                        (uu___379_13673.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___379_13673.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___379_13673.tcenv);
                                                      wl_implicits =
                                                        (uu___379_13673.wl_implicits)
                                                    }  in
                                                  let uu____13674 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13674
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13680 =
                                                  solve_t env eq_prob
                                                    (let uu___380_13682 = wl'
                                                        in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___380_13682.wl_deferred);
                                                       ctr =
                                                         (uu___380_13682.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___380_13682.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___380_13682.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___380_13682.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____13680 with
                                                | Success (uu____13684,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___381_13687 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___381_13687.wl_deferred);
                                                        ctr =
                                                          (uu___381_13687.ctr);
                                                        defer_ok =
                                                          (uu___381_13687.defer_ok);
                                                        smt_ok =
                                                          (uu___381_13687.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___381_13687.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___381_13687.tcenv);
                                                        wl_implicits =
                                                          (uu___381_13687.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___382_13689 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___382_13689.attempting);
                                                        wl_deferred =
                                                          (uu___382_13689.wl_deferred);
                                                        ctr =
                                                          (uu___382_13689.ctr);
                                                        defer_ok =
                                                          (uu___382_13689.defer_ok);
                                                        smt_ok =
                                                          (uu___382_13689.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___382_13689.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___382_13689.tcenv);
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
                                                    let uu____13705 =
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
                                                    ((let uu____13719 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____13719
                                                      then
                                                        let uu____13724 =
                                                          let uu____13726 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____13726
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13724
                                                      else ());
                                                     (let uu____13739 =
                                                        let uu____13754 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____13754)
                                                         in
                                                      match uu____13739 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____13776))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13802 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____13802
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
                                                                  let uu____13822
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____13822))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13847 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____13847
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
                                                                    let uu____13867
                                                                    =
                                                                    let uu____13872
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____13872
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____13867
                                                                    [] wl2
                                                                     in
                                                                  let uu____13878
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____13878))))
                                                      | uu____13879 ->
                                                          giveup env
                                                            (Prims.strcat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____13895 when flip ->
                               let uu____13896 =
                                 let uu____13898 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____13900 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____13898 uu____13900
                                  in
                               failwith uu____13896
                           | uu____13903 ->
                               let uu____13904 =
                                 let uu____13906 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____13908 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____13906 uu____13908
                                  in
                               failwith uu____13904)))))

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
                      (fun uu____13944  ->
                         match uu____13944 with
                         | (x,i) ->
                             let uu____13963 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____13963, i)) bs_lhs
                     in
                  let uu____13966 = lhs  in
                  match uu____13966 with
                  | (uu____13967,u_lhs,uu____13969) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14066 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14076 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14076, univ)
                             in
                          match uu____14066 with
                          | (k,univ) ->
                              let uu____14083 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14083 with
                               | (uu____14100,u,wl3) ->
                                   let uu____14103 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14103, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14129 =
                              let uu____14142 =
                                let uu____14153 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14153 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____14204  ->
                                   fun uu____14205  ->
                                     match (uu____14204, uu____14205) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____14306 =
                                           let uu____14313 =
                                             let uu____14316 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____14316
                                              in
                                           copy_uvar u_lhs [] uu____14313 wl2
                                            in
                                         (match uu____14306 with
                                          | (uu____14345,t_a,wl3) ->
                                              let uu____14348 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____14348 with
                                               | (uu____14367,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14142
                                ([], wl1)
                               in
                            (match uu____14129 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___383_14423 = ct  in
                                   let uu____14424 =
                                     let uu____14427 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14427
                                      in
                                   let uu____14442 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___383_14423.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___383_14423.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14424;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14442;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___383_14423.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___384_14460 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___384_14460.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___384_14460.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14463 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____14463 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14525 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14525 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____14536 =
                                          let uu____14541 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____14541)  in
                                        TERM uu____14536  in
                                      let uu____14542 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____14542 with
                                       | (sub_prob,wl3) ->
                                           let uu____14556 =
                                             let uu____14557 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____14557
                                              in
                                           solve env uu____14556))
                             | (x,imp)::formals2 ->
                                 let uu____14579 =
                                   let uu____14586 =
                                     let uu____14589 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____14589
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14586 wl1
                                    in
                                 (match uu____14579 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____14610 =
                                          let uu____14613 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14613
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14610 u_x
                                         in
                                      let uu____14614 =
                                        let uu____14617 =
                                          let uu____14620 =
                                            let uu____14621 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____14621, imp)  in
                                          [uu____14620]  in
                                        FStar_List.append bs_terms
                                          uu____14617
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14614 formals2 wl2)
                              in
                           let uu____14648 = occurs_check u_lhs arrow1  in
                           (match uu____14648 with
                            | (uu____14661,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14677 =
                                    let uu____14679 = FStar_Option.get msg
                                       in
                                    Prims.strcat "occurs-check failed: "
                                      uu____14679
                                     in
                                  giveup_or_defer env orig wl uu____14677
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
              (let uu____14712 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____14712
               then
                 let uu____14717 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____14720 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14717 (rel_to_string (p_rel orig)) uu____14720
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____14847 = rhs wl1 scope env1 subst1  in
                     (match uu____14847 with
                      | (rhs_prob,wl2) ->
                          ((let uu____14868 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____14868
                            then
                              let uu____14873 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____14873
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____14951 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____14951 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___385_14953 = hd1  in
                       let uu____14954 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___385_14953.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___385_14953.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____14954
                       }  in
                     let hd21 =
                       let uu___386_14958 = hd2  in
                       let uu____14959 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___386_14958.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___386_14958.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____14959
                       }  in
                     let uu____14962 =
                       let uu____14967 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____14967
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____14962 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____14988 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____14988
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____14995 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____14995 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15062 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15062
                                  in
                               ((let uu____15080 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15080
                                 then
                                   let uu____15085 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15087 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15085
                                     uu____15087
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____15120 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15156 = aux wl [] env [] bs1 bs2  in
               match uu____15156 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15211 = attempt sub_probs wl2  in
                   solve env uu____15211)

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
            let uu___387_15232 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___387_15232.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___387_15232.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15245 = try_solve env wl'  in
          match uu____15245 with
          | Success (uu____15246,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___388_15250 = wl  in
                  {
                    attempting = (uu___388_15250.attempting);
                    wl_deferred = (uu___388_15250.wl_deferred);
                    ctr = (uu___388_15250.ctr);
                    defer_ok = (uu___388_15250.defer_ok);
                    smt_ok = (uu___388_15250.smt_ok);
                    umax_heuristic_ok = (uu___388_15250.umax_heuristic_ok);
                    tcenv = (uu___388_15250.tcenv);
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
        (let uu____15262 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15262 wl)

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
              let uu____15276 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15276 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15310 = lhs1  in
              match uu____15310 with
              | (uu____15313,ctx_u,uu____15315) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15323 ->
                        let uu____15324 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15324 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15373 = quasi_pattern env1 lhs1  in
              match uu____15373 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15407) ->
                  let uu____15412 = lhs1  in
                  (match uu____15412 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15427 = occurs_check ctx_u rhs1  in
                       (match uu____15427 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15478 =
                                let uu____15486 =
                                  let uu____15488 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15488
                                   in
                                FStar_Util.Inl uu____15486  in
                              (uu____15478, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15516 =
                                 let uu____15518 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15518  in
                               if uu____15516
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15545 =
                                    let uu____15553 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15553  in
                                  let uu____15559 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____15545, uu____15559)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____15603 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____15603 with
              | (rhs_hd,args) ->
                  let uu____15646 = FStar_Util.prefix args  in
                  (match uu____15646 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15718 = lhs1  in
                       (match uu____15718 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____15722 =
                              let uu____15733 =
                                let uu____15740 =
                                  let uu____15743 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____15743
                                   in
                                copy_uvar u_lhs [] uu____15740 wl1  in
                              match uu____15733 with
                              | (uu____15770,t_last_arg,wl2) ->
                                  let uu____15773 =
                                    let uu____15780 =
                                      let uu____15781 =
                                        let uu____15790 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____15790]  in
                                      FStar_List.append bs_lhs uu____15781
                                       in
                                    copy_uvar u_lhs uu____15780 t_res_lhs wl2
                                     in
                                  (match uu____15773 with
                                   | (uu____15825,lhs',wl3) ->
                                       let uu____15828 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____15828 with
                                        | (uu____15845,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____15722 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____15866 =
                                     let uu____15867 =
                                       let uu____15872 =
                                         let uu____15873 =
                                           let uu____15876 =
                                             let uu____15881 =
                                               let uu____15882 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____15882]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____15881
                                              in
                                           uu____15876
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____15873
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____15872)  in
                                     TERM uu____15867  in
                                   [uu____15866]  in
                                 let uu____15909 =
                                   let uu____15916 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____15916 with
                                   | (p1,wl3) ->
                                       let uu____15936 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____15936 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____15909 with
                                  | (sub_probs,wl3) ->
                                      let uu____15968 =
                                        let uu____15969 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____15969  in
                                      solve env1 uu____15968))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16003 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16003 with
                | (uu____16021,args) ->
                    (match args with | [] -> false | uu____16057 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16076 =
                  let uu____16077 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16077.FStar_Syntax_Syntax.n  in
                match uu____16076 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16081 -> true
                | uu____16097 -> false  in
              let uu____16099 = quasi_pattern env1 lhs1  in
              match uu____16099 with
              | FStar_Pervasives_Native.None  ->
                  let uu____16110 =
                    let uu____16112 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                      uu____16112
                     in
                  giveup_or_defer env1 orig1 wl1 uu____16110
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16121 = is_app rhs1  in
                  if uu____16121
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____16126 = is_arrow rhs1  in
                     if uu____16126
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____16131 =
                          let uu____16133 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heuristic cannot solve %s; rhs not an app or arrow"
                            uu____16133
                           in
                        giveup_or_defer env1 orig1 wl1 uu____16131))
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
                let uu____16144 = lhs  in
                (match uu____16144 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16148 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16148 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16166 =
                              let uu____16170 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16170
                               in
                            FStar_All.pipe_right uu____16166
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16191 = occurs_check ctx_uv rhs1  in
                          (match uu____16191 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16220 =
                                   let uu____16222 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____16222
                                    in
                                 giveup_or_defer env orig wl uu____16220
                               else
                                 (let uu____16228 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____16228
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____16235 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____16235
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____16239 =
                                         let uu____16241 =
                                           names_to_string1 fvs2  in
                                         let uu____16243 =
                                           names_to_string1 fvs1  in
                                         let uu____16245 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____16241 uu____16243
                                           uu____16245
                                          in
                                       giveup_or_defer env orig wl
                                         uu____16239)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16257 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____16264 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16264 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16290 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16290
                             | (FStar_Util.Inl msg,uu____16292) ->
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
                  (let uu____16337 =
                     let uu____16354 = quasi_pattern env lhs  in
                     let uu____16361 = quasi_pattern env rhs  in
                     (uu____16354, uu____16361)  in
                   match uu____16337 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16404 = lhs  in
                       (match uu____16404 with
                        | ({ FStar_Syntax_Syntax.n = uu____16405;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____16407;_},u_lhs,uu____16409)
                            ->
                            let uu____16412 = rhs  in
                            (match uu____16412 with
                             | (uu____16413,u_rhs,uu____16415) ->
                                 let uu____16416 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16416
                                 then
                                   let uu____16423 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16423
                                 else
                                   (let uu____16426 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16426 with
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
                                        let uu____16458 =
                                          let uu____16465 =
                                            let uu____16468 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16468
                                             in
                                          new_uvar
                                            (Prims.strcat "flex-flex quasi:"
                                               (Prims.strcat "\tlhs="
                                                  (Prims.strcat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.strcat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16465
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____16458 with
                                         | (uu____16480,w,wl1) ->
                                             let w_app =
                                               let uu____16486 =
                                                 let uu____16491 =
                                                   FStar_List.map
                                                     (fun uu____16502  ->
                                                        match uu____16502
                                                        with
                                                        | (z,uu____16510) ->
                                                            let uu____16515 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____16515) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____16491
                                                  in
                                               uu____16486
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16519 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16519
                                               then
                                                 let uu____16524 =
                                                   let uu____16528 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16530 =
                                                     let uu____16534 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____16536 =
                                                       let uu____16540 =
                                                         term_to_string w  in
                                                       let uu____16542 =
                                                         let uu____16546 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____16555 =
                                                           let uu____16559 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____16568 =
                                                             let uu____16572
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____16572]
                                                              in
                                                           uu____16559 ::
                                                             uu____16568
                                                            in
                                                         uu____16546 ::
                                                           uu____16555
                                                          in
                                                       uu____16540 ::
                                                         uu____16542
                                                        in
                                                     uu____16534 ::
                                                       uu____16536
                                                      in
                                                   uu____16528 :: uu____16530
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16524
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____16589 =
                                                     let uu____16594 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____16594)  in
                                                   TERM uu____16589  in
                                                 let uu____16595 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____16595
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____16603 =
                                                        let uu____16608 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____16608)
                                                         in
                                                      TERM uu____16603  in
                                                    [s1; s2])
                                                  in
                                               let uu____16609 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____16609))))))
                   | uu____16610 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____16681 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____16681
            then
              let uu____16686 = FStar_Syntax_Print.term_to_string t1  in
              let uu____16688 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____16690 = FStar_Syntax_Print.term_to_string t2  in
              let uu____16692 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____16686 uu____16688 uu____16690 uu____16692
            else ());
           (let uu____16703 = FStar_Syntax_Util.head_and_args t1  in
            match uu____16703 with
            | (head1,args1) ->
                let uu____16746 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____16746 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____16816 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____16816 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              k false (defer "universe constraints" orig wl3))
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____16846 =
                         let uu____16848 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____16850 = args_to_string args1  in
                         let uu____16854 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____16856 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____16848 uu____16850 uu____16854 uu____16856
                          in
                       giveup env1 uu____16846 orig
                     else
                       (let uu____16863 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____16872 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____16872 = FStar_Syntax_Util.Equal)
                           in
                        if uu____16863
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___389_16876 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___389_16876.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___389_16876.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___389_16876.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___389_16876.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___389_16876.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___389_16876.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___389_16876.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___389_16876.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____16886 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____16886
                                    else solve env1 wl2))
                        else
                          (let uu____16891 = base_and_refinement env1 t1  in
                           match uu____16891 with
                           | (base1,refinement1) ->
                               let uu____16916 = base_and_refinement env1 t2
                                  in
                               (match uu____16916 with
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
                                           let uu____17081 =
                                             FStar_List.fold_right
                                               (fun uu____17121  ->
                                                  fun uu____17122  ->
                                                    match (uu____17121,
                                                            uu____17122)
                                                    with
                                                    | (((a1,uu____17174),
                                                        (a2,uu____17176)),
                                                       (probs,wl3)) ->
                                                        let uu____17225 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17225
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17081 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17268 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17268
                                                 then
                                                   let uu____17273 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17273
                                                 else ());
                                                (let uu____17279 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17279
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
                                                    (let uu____17306 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17306 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17322 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17322
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17330 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17330))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____17354 =
                                                    mk_sub_probs wl3  in
                                                  match uu____17354 with
                                                  | (subprobs,wl4) ->
                                                      let wl5 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          [] wl4
                                                         in
                                                      let uu____17368 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____17368)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17394 =
                                           match uu____17394 with
                                           | (prob,reason) ->
                                               ((let uu____17405 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17405
                                                 then
                                                   let uu____17410 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____17412 =
                                                     prob_to_string env2 prob
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____17410 uu____17412
                                                     reason
                                                 else ());
                                                (let uu____17417 =
                                                   let uu____17426 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____17429 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____17426, uu____17429)
                                                    in
                                                 match uu____17417 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____17442 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____17442 with
                                                      | (head1',uu____17460)
                                                          ->
                                                          let uu____17485 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____17485
                                                           with
                                                           | (head2',uu____17503)
                                                               ->
                                                               let uu____17528
                                                                 =
                                                                 let uu____17533
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____17534
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____17533,
                                                                   uu____17534)
                                                                  in
                                                               (match uu____17528
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____17536
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17536
                                                                    then
                                                                    let uu____17541
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____17543
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____17545
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____17547
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17541
                                                                    uu____17543
                                                                    uu____17545
                                                                    uu____17547
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____17552
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___390_17560
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___390_17560.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___390_17560.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___390_17560.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___390_17560.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___390_17560.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___390_17560.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___390_17560.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___390_17560.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____17562
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17562
                                                                    then
                                                                    let uu____17567
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____17567
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____17572 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____17584 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____17584 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____17592 =
                                             let uu____17593 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____17593.FStar_Syntax_Syntax.n
                                              in
                                           match uu____17592 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____17598 -> false  in
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
                                          | uu____17601 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____17604 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___391_17640 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___391_17640.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___391_17640.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___391_17640.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___391_17640.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___391_17640.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___391_17640.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___391_17640.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___391_17640.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____17716 = destruct_flex_t scrutinee wl1  in
             match uu____17716 with
             | ((_t,uv,_args),wl2) ->
                 let uu____17727 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____17727 with
                  | (xs,pat_term,uu____17743,uu____17744) ->
                      let uu____17749 =
                        FStar_List.fold_left
                          (fun uu____17772  ->
                             fun x  ->
                               match uu____17772 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____17793 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____17793 with
                                    | (uu____17812,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____17749 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____17833 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____17833 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___392_17850 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___392_17850.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___392_17850.umax_heuristic_ok);
                                    tcenv = (uu___392_17850.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____17862 = solve env1 wl'  in
                                (match uu____17862 with
                                 | Success (uu____17865,imps) ->
                                     let wl'1 =
                                       let uu___393_17868 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___393_17868.wl_deferred);
                                         ctr = (uu___393_17868.ctr);
                                         defer_ok = (uu___393_17868.defer_ok);
                                         smt_ok = (uu___393_17868.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___393_17868.umax_heuristic_ok);
                                         tcenv = (uu___393_17868.tcenv);
                                         wl_implicits =
                                           (uu___393_17868.wl_implicits)
                                       }  in
                                     let uu____17869 = solve env1 wl'1  in
                                     (match uu____17869 with
                                      | Success (uu____17872,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___394_17876 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___394_17876.attempting);
                                                 wl_deferred =
                                                   (uu___394_17876.wl_deferred);
                                                 ctr = (uu___394_17876.ctr);
                                                 defer_ok =
                                                   (uu___394_17876.defer_ok);
                                                 smt_ok =
                                                   (uu___394_17876.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___394_17876.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___394_17876.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____17877 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____17884 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____17907 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____17907
                 then
                   let uu____17912 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____17914 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____17912 uu____17914
                 else ());
                (let uu____17919 =
                   let uu____17940 =
                     let uu____17949 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____17949)  in
                   let uu____17956 =
                     let uu____17965 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____17965)  in
                   (uu____17940, uu____17956)  in
                 match uu____17919 with
                 | ((uu____17995,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____17998;
                                   FStar_Syntax_Syntax.vars = uu____17999;_}),
                    (s,t)) ->
                     let uu____18070 =
                       let uu____18072 = is_flex scrutinee  in
                       Prims.op_Negation uu____18072  in
                     if uu____18070
                     then
                       ((let uu____18083 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18083
                         then
                           let uu____18088 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18088
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18107 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18107
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18122 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18122
                           then
                             let uu____18127 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18129 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18127 uu____18129
                           else ());
                          (let pat_discriminates uu___350_18154 =
                             match uu___350_18154 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18170;
                                  FStar_Syntax_Syntax.p = uu____18171;_},FStar_Pervasives_Native.None
                                ,uu____18172) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18186;
                                  FStar_Syntax_Syntax.p = uu____18187;_},FStar_Pervasives_Native.None
                                ,uu____18188) -> true
                             | uu____18215 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18318 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18318 with
                                       | (uu____18320,uu____18321,t') ->
                                           let uu____18339 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18339 with
                                            | (FullMatch ,uu____18351) ->
                                                true
                                            | (HeadMatch
                                               uu____18365,uu____18366) ->
                                                true
                                            | uu____18381 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18418 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18418
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18429 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18429 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18517,uu____18518) ->
                                       branches1
                                   | uu____18663 -> branches  in
                                 let uu____18718 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____18727 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____18727 with
                                        | (p,uu____18731,uu____18732) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_8  -> FStar_Util.Inr _0_8)
                                   uu____18718))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____18790 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____18790 with
                                | (p,uu____18799,e) ->
                                    ((let uu____18818 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____18818
                                      then
                                        let uu____18823 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____18825 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____18823 uu____18825
                                      else ());
                                     (let uu____18830 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _0_9  -> FStar_Util.Inr _0_9)
                                        uu____18830)))))
                 | ((s,t),(uu____18847,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____18850;
                                         FStar_Syntax_Syntax.vars =
                                           uu____18851;_}))
                     ->
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
                          (let pat_discriminates uu___350_19004 =
                             match uu___350_19004 with
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
                                   (fun _0_10  -> FStar_Util.Inr _0_10)
                                   uu____19568))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19640 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19640 with
                                | (p,uu____19649,e) ->
                                    ((let uu____19668 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19668
                                      then
                                        let uu____19673 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19675 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19673 uu____19675
                                      else ());
                                     (let uu____19680 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _0_11  -> FStar_Util.Inr _0_11)
                                        uu____19680)))))
                 | uu____19695 ->
                     ((let uu____19717 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____19717
                       then
                         let uu____19722 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____19724 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____19722 uu____19724
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____19770 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____19770
            then
              let uu____19775 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____19777 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____19779 = FStar_Syntax_Print.term_to_string t1  in
              let uu____19781 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____19775 uu____19777 uu____19779 uu____19781
            else ());
           (let uu____19786 = head_matches_delta env1 wl1 t1 t2  in
            match uu____19786 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____19817,uu____19818) ->
                     let rec may_relate head3 =
                       let uu____19846 =
                         let uu____19847 = FStar_Syntax_Subst.compress head3
                            in
                         uu____19847.FStar_Syntax_Syntax.n  in
                       match uu____19846 with
                       | FStar_Syntax_Syntax.Tm_name uu____19851 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____19853 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____19878 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____19878 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____19880 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____19883
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____19884 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____19887,uu____19888) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____19930) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____19936) ->
                           may_relate t
                       | uu____19941 -> false  in
                     let uu____19943 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____19943 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____19964 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____19964
                          then
                            let uu____19967 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____19967 with
                             | (guard,wl2) ->
                                 let uu____19974 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____19974)
                          else
                            (let uu____19977 =
                               let uu____19979 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____19981 =
                                 let uu____19983 =
                                   let uu____19987 =
                                     delta_depth_of_term env1 head1  in
                                   FStar_Util.bind_opt uu____19987
                                     (fun x  ->
                                        let uu____19994 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____19994)
                                    in
                                 FStar_Util.dflt "" uu____19983  in
                               let uu____19999 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               let uu____20001 =
                                 let uu____20003 =
                                   let uu____20007 =
                                     delta_depth_of_term env1 head2  in
                                   FStar_Util.bind_opt uu____20007
                                     (fun x  ->
                                        let uu____20014 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____20014)
                                    in
                                 FStar_Util.dflt "" uu____20003  in
                               FStar_Util.format4
                                 "head mismatch (%s (%s) vs %s (%s))"
                                 uu____19979 uu____19981 uu____19999
                                 uu____20001
                                in
                             giveup env1 uu____19977 orig))
                 | (HeadMatch (true ),uu____20020) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20035 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20035 with
                        | (guard,wl2) ->
                            let uu____20042 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20042)
                     else
                       (let uu____20045 =
                          let uu____20047 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____20049 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____20047 uu____20049
                           in
                        giveup env1 uu____20045 orig)
                 | (uu____20052,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___395_20066 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___395_20066.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___395_20066.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___395_20066.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___395_20066.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___395_20066.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___395_20066.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___395_20066.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___395_20066.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20093 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20093
          then
            let uu____20096 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20096
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20102 =
                let uu____20105 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20105  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20102 t1);
             (let uu____20124 =
                let uu____20127 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20127  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20124 t2);
             (let uu____20146 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20146
              then
                let uu____20150 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20152 =
                  let uu____20154 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20156 =
                    let uu____20158 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____20158  in
                  Prims.strcat uu____20154 uu____20156  in
                let uu____20161 =
                  let uu____20163 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20165 =
                    let uu____20167 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____20167  in
                  Prims.strcat uu____20163 uu____20165  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20150 uu____20152 uu____20161
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20174,uu____20175) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20199,FStar_Syntax_Syntax.Tm_delayed uu____20200) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20224,uu____20225) ->
                  let uu____20252 =
                    let uu___396_20253 = problem  in
                    let uu____20254 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___396_20253.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20254;
                      FStar_TypeChecker_Common.relation =
                        (uu___396_20253.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___396_20253.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___396_20253.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___396_20253.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___396_20253.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___396_20253.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___396_20253.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___396_20253.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20252 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20255,uu____20256) ->
                  let uu____20263 =
                    let uu___397_20264 = problem  in
                    let uu____20265 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___397_20264.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20265;
                      FStar_TypeChecker_Common.relation =
                        (uu___397_20264.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___397_20264.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___397_20264.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___397_20264.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___397_20264.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___397_20264.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___397_20264.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___397_20264.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20263 wl
              | (uu____20266,FStar_Syntax_Syntax.Tm_ascribed uu____20267) ->
                  let uu____20294 =
                    let uu___398_20295 = problem  in
                    let uu____20296 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___398_20295.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___398_20295.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___398_20295.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20296;
                      FStar_TypeChecker_Common.element =
                        (uu___398_20295.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___398_20295.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___398_20295.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___398_20295.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___398_20295.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___398_20295.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20294 wl
              | (uu____20297,FStar_Syntax_Syntax.Tm_meta uu____20298) ->
                  let uu____20305 =
                    let uu___399_20306 = problem  in
                    let uu____20307 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___399_20306.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___399_20306.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___399_20306.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20307;
                      FStar_TypeChecker_Common.element =
                        (uu___399_20306.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___399_20306.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___399_20306.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___399_20306.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___399_20306.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___399_20306.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20305 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____20309),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____20311)) ->
                  let uu____20320 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____20320
              | (FStar_Syntax_Syntax.Tm_bvar uu____20321,uu____20322) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____20324,FStar_Syntax_Syntax.Tm_bvar uu____20325) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___351_20395 =
                    match uu___351_20395 with
                    | [] -> c
                    | bs ->
                        let uu____20423 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____20423
                     in
                  let uu____20434 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____20434 with
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
                                    let uu____20583 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____20583
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
                  let mk_t t l uu___352_20672 =
                    match uu___352_20672 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____20714 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____20714 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____20859 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____20860 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____20859
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____20860 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____20862,uu____20863) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____20894 -> true
                    | uu____20914 -> false  in
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
                      (let uu____20974 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___400_20982 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___400_20982.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___400_20982.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___400_20982.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___400_20982.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___400_20982.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___400_20982.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___400_20982.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___400_20982.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___400_20982.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___400_20982.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___400_20982.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___400_20982.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___400_20982.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___400_20982.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___400_20982.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___400_20982.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___400_20982.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___400_20982.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___400_20982.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___400_20982.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___400_20982.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___400_20982.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___400_20982.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___400_20982.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___400_20982.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___400_20982.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___400_20982.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___400_20982.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___400_20982.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___400_20982.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___400_20982.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___400_20982.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___400_20982.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___400_20982.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___400_20982.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___400_20982.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___400_20982.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___400_20982.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___400_20982.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___400_20982.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____20974 with
                       | (uu____20987,ty,uu____20989) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____20998 =
                                 let uu____20999 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____20999.FStar_Syntax_Syntax.n  in
                               match uu____20998 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21002 ->
                                   let uu____21009 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21009
                               | uu____21010 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21013 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21013
                             then
                               let uu____21018 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21020 =
                                 let uu____21022 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21022
                                  in
                               let uu____21023 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21018 uu____21020 uu____21023
                             else ());
                            r1))
                     in
                  let uu____21028 =
                    let uu____21045 = maybe_eta t1  in
                    let uu____21052 = maybe_eta t2  in
                    (uu____21045, uu____21052)  in
                  (match uu____21028 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___401_21094 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___401_21094.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___401_21094.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___401_21094.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___401_21094.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___401_21094.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___401_21094.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___401_21094.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___401_21094.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21115 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21115
                       then
                         let uu____21118 = destruct_flex_t not_abs wl  in
                         (match uu____21118 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___402_21135 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___402_21135.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___402_21135.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___402_21135.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___402_21135.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___402_21135.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___402_21135.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___402_21135.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___402_21135.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21159 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21159
                       then
                         let uu____21162 = destruct_flex_t not_abs wl  in
                         (match uu____21162 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___402_21179 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___402_21179.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___402_21179.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___402_21179.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___402_21179.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___402_21179.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___402_21179.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___402_21179.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___402_21179.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____21183 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21201,FStar_Syntax_Syntax.Tm_abs uu____21202) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21233 -> true
                    | uu____21253 -> false  in
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
                      (let uu____21313 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___400_21321 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___400_21321.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___400_21321.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___400_21321.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___400_21321.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___400_21321.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___400_21321.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___400_21321.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___400_21321.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___400_21321.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___400_21321.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___400_21321.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___400_21321.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___400_21321.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___400_21321.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___400_21321.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___400_21321.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___400_21321.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___400_21321.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___400_21321.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___400_21321.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___400_21321.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___400_21321.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___400_21321.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___400_21321.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___400_21321.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___400_21321.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___400_21321.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___400_21321.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___400_21321.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___400_21321.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___400_21321.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___400_21321.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___400_21321.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___400_21321.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___400_21321.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___400_21321.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___400_21321.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___400_21321.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___400_21321.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___400_21321.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____21313 with
                       | (uu____21326,ty,uu____21328) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21337 =
                                 let uu____21338 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21338.FStar_Syntax_Syntax.n  in
                               match uu____21337 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21341 ->
                                   let uu____21348 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21348
                               | uu____21349 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21352 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21352
                             then
                               let uu____21357 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21359 =
                                 let uu____21361 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21361
                                  in
                               let uu____21362 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21357 uu____21359 uu____21362
                             else ());
                            r1))
                     in
                  let uu____21367 =
                    let uu____21384 = maybe_eta t1  in
                    let uu____21391 = maybe_eta t2  in
                    (uu____21384, uu____21391)  in
                  (match uu____21367 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___401_21433 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___401_21433.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___401_21433.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___401_21433.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___401_21433.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___401_21433.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___401_21433.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___401_21433.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___401_21433.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21454 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21454
                       then
                         let uu____21457 = destruct_flex_t not_abs wl  in
                         (match uu____21457 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___402_21474 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___402_21474.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___402_21474.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___402_21474.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___402_21474.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___402_21474.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___402_21474.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___402_21474.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___402_21474.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21498 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21498
                       then
                         let uu____21501 = destruct_flex_t not_abs wl  in
                         (match uu____21501 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___402_21518 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___402_21518.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___402_21518.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___402_21518.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___402_21518.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___402_21518.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___402_21518.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___402_21518.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___402_21518.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____21522 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____21552 =
                    let uu____21557 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____21557 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___403_21585 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___403_21585.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___403_21585.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___404_21587 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___404_21587.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___404_21587.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____21588,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___403_21603 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___403_21603.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___403_21603.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___404_21605 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___404_21605.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___404_21605.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____21606 -> (x1, x2)  in
                  (match uu____21552 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____21625 = as_refinement false env t11  in
                       (match uu____21625 with
                        | (x12,phi11) ->
                            let uu____21633 = as_refinement false env t21  in
                            (match uu____21633 with
                             | (x22,phi21) ->
                                 ((let uu____21642 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21642
                                   then
                                     ((let uu____21647 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____21649 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21651 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____21647
                                         uu____21649 uu____21651);
                                      (let uu____21654 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____21656 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21658 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____21654
                                         uu____21656 uu____21658))
                                   else ());
                                  (let uu____21663 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____21663 with
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
                                         let uu____21734 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____21734
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____21746 =
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
                                         (let uu____21759 =
                                            let uu____21762 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____21762
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____21759
                                            (p_guard base_prob));
                                         (let uu____21781 =
                                            let uu____21784 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____21784
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____21781
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____21803 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____21803)
                                          in
                                       let has_uvars =
                                         (let uu____21808 =
                                            let uu____21810 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____21810
                                             in
                                          Prims.op_Negation uu____21808) ||
                                           (let uu____21814 =
                                              let uu____21816 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____21816
                                               in
                                            Prims.op_Negation uu____21814)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____21820 =
                                           let uu____21825 =
                                             let uu____21834 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____21834]  in
                                           mk_t_problem wl1 uu____21825 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____21820 with
                                          | (ref_prob,wl2) ->
                                              let uu____21856 =
                                                solve env1
                                                  (let uu___405_21858 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___405_21858.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___405_21858.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___405_21858.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___405_21858.tcenv);
                                                     wl_implicits =
                                                       (uu___405_21858.wl_implicits)
                                                   })
                                                 in
                                              (match uu____21856 with
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
                                               | Success uu____21875 ->
                                                   let guard =
                                                     let uu____21883 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____21883
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___406_21892 = wl3
                                                        in
                                                     {
                                                       attempting =
                                                         (uu___406_21892.attempting);
                                                       wl_deferred =
                                                         (uu___406_21892.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            (Prims.parse_int "1"));
                                                       defer_ok =
                                                         (uu___406_21892.defer_ok);
                                                       smt_ok =
                                                         (uu___406_21892.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___406_21892.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___406_21892.tcenv);
                                                       wl_implicits =
                                                         (uu___406_21892.wl_implicits)
                                                     }  in
                                                   let uu____21894 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____21894))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____21897,FStar_Syntax_Syntax.Tm_uvar uu____21898) ->
                  let uu____21923 = destruct_flex_t t1 wl  in
                  (match uu____21923 with
                   | (f1,wl1) ->
                       let uu____21930 = destruct_flex_t t2 wl1  in
                       (match uu____21930 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21937;
                    FStar_Syntax_Syntax.pos = uu____21938;
                    FStar_Syntax_Syntax.vars = uu____21939;_},uu____21940),FStar_Syntax_Syntax.Tm_uvar
                 uu____21941) ->
                  let uu____21990 = destruct_flex_t t1 wl  in
                  (match uu____21990 with
                   | (f1,wl1) ->
                       let uu____21997 = destruct_flex_t t2 wl1  in
                       (match uu____21997 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22004,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22005;
                    FStar_Syntax_Syntax.pos = uu____22006;
                    FStar_Syntax_Syntax.vars = uu____22007;_},uu____22008))
                  ->
                  let uu____22057 = destruct_flex_t t1 wl  in
                  (match uu____22057 with
                   | (f1,wl1) ->
                       let uu____22064 = destruct_flex_t t2 wl1  in
                       (match uu____22064 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22071;
                    FStar_Syntax_Syntax.pos = uu____22072;
                    FStar_Syntax_Syntax.vars = uu____22073;_},uu____22074),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22075;
                    FStar_Syntax_Syntax.pos = uu____22076;
                    FStar_Syntax_Syntax.vars = uu____22077;_},uu____22078))
                  ->
                  let uu____22151 = destruct_flex_t t1 wl  in
                  (match uu____22151 with
                   | (f1,wl1) ->
                       let uu____22158 = destruct_flex_t t2 wl1  in
                       (match uu____22158 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22165,uu____22166) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22179 = destruct_flex_t t1 wl  in
                  (match uu____22179 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22186;
                    FStar_Syntax_Syntax.pos = uu____22187;
                    FStar_Syntax_Syntax.vars = uu____22188;_},uu____22189),uu____22190)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22227 = destruct_flex_t t1 wl  in
                  (match uu____22227 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22234,FStar_Syntax_Syntax.Tm_uvar uu____22235) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22248,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22249;
                    FStar_Syntax_Syntax.pos = uu____22250;
                    FStar_Syntax_Syntax.vars = uu____22251;_},uu____22252))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22289,FStar_Syntax_Syntax.Tm_arrow uu____22290) ->
                  solve_t' env
                    (let uu___407_22318 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___407_22318.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___407_22318.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___407_22318.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___407_22318.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___407_22318.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___407_22318.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___407_22318.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___407_22318.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___407_22318.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22319;
                    FStar_Syntax_Syntax.pos = uu____22320;
                    FStar_Syntax_Syntax.vars = uu____22321;_},uu____22322),FStar_Syntax_Syntax.Tm_arrow
                 uu____22323) ->
                  solve_t' env
                    (let uu___407_22375 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___407_22375.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___407_22375.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___407_22375.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___407_22375.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___407_22375.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___407_22375.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___407_22375.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___407_22375.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___407_22375.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22376,FStar_Syntax_Syntax.Tm_uvar uu____22377) ->
                  let uu____22390 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22390
              | (uu____22391,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22392;
                    FStar_Syntax_Syntax.pos = uu____22393;
                    FStar_Syntax_Syntax.vars = uu____22394;_},uu____22395))
                  ->
                  let uu____22432 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22432
              | (FStar_Syntax_Syntax.Tm_uvar uu____22433,uu____22434) ->
                  let uu____22447 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22447
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22448;
                    FStar_Syntax_Syntax.pos = uu____22449;
                    FStar_Syntax_Syntax.vars = uu____22450;_},uu____22451),uu____22452)
                  ->
                  let uu____22489 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22489
              | (FStar_Syntax_Syntax.Tm_refine uu____22490,uu____22491) ->
                  let t21 =
                    let uu____22499 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____22499  in
                  solve_t env
                    (let uu___408_22525 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___408_22525.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___408_22525.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___408_22525.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___408_22525.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___408_22525.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___408_22525.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___408_22525.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___408_22525.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___408_22525.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22526,FStar_Syntax_Syntax.Tm_refine uu____22527) ->
                  let t11 =
                    let uu____22535 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22535  in
                  solve_t env
                    (let uu___409_22561 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___409_22561.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___409_22561.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___409_22561.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___409_22561.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___409_22561.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___409_22561.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___409_22561.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___409_22561.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___409_22561.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____22643 =
                    let uu____22644 = guard_of_prob env wl problem t1 t2  in
                    match uu____22644 with
                    | (guard,wl1) ->
                        let uu____22651 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____22651
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____22870 = br1  in
                        (match uu____22870 with
                         | (p1,w1,uu____22899) ->
                             let uu____22916 = br2  in
                             (match uu____22916 with
                              | (p2,w2,uu____22939) ->
                                  let uu____22944 =
                                    let uu____22946 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____22946  in
                                  if uu____22944
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____22973 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____22973 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23010 = br2  in
                                         (match uu____23010 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23043 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23043
                                                 in
                                              let uu____23048 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23079,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23100) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23159 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23159 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23048
                                                (fun uu____23231  ->
                                                   match uu____23231 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23268 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23268
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____23289
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____23289
                                                              then
                                                                let uu____23294
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____23296
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____23294
                                                                  uu____23296
                                                              else ());
                                                             (let uu____23302
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____23302
                                                                (fun
                                                                   uu____23338
                                                                    ->
                                                                   match uu____23338
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
                    | uu____23467 -> FStar_Pervasives_Native.None  in
                  let uu____23508 = solve_branches wl brs1 brs2  in
                  (match uu____23508 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____23559 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____23559 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____23593 =
                                FStar_List.map
                                  (fun uu____23605  ->
                                     match uu____23605 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____23593  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____23614 =
                              let uu____23615 =
                                let uu____23616 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____23616
                                  (let uu___410_23624 = wl3  in
                                   {
                                     attempting = (uu___410_23624.attempting);
                                     wl_deferred =
                                       (uu___410_23624.wl_deferred);
                                     ctr = (uu___410_23624.ctr);
                                     defer_ok = (uu___410_23624.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___410_23624.umax_heuristic_ok);
                                     tcenv = (uu___410_23624.tcenv);
                                     wl_implicits =
                                       (uu___410_23624.wl_implicits)
                                   })
                                 in
                              solve env uu____23615  in
                            (match uu____23614 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____23629 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____23636,uu____23637) ->
                  let head1 =
                    let uu____23661 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23661
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23707 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23707
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23753 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23753
                    then
                      let uu____23757 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23759 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23761 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23757 uu____23759 uu____23761
                    else ());
                   (let no_free_uvars t =
                      (let uu____23775 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23775) &&
                        (let uu____23779 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23779)
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
                      let uu____23796 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23796 = FStar_Syntax_Util.Equal  in
                    let uu____23797 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23797
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23801 = equal t1 t2  in
                         (if uu____23801
                          then
                            let uu____23804 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____23804
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23809 =
                            let uu____23816 = equal t1 t2  in
                            if uu____23816
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23829 = mk_eq2 wl env orig t1 t2  in
                               match uu____23829 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____23809 with
                          | (guard,wl1) ->
                              let uu____23850 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____23850))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____23853,uu____23854) ->
                  let head1 =
                    let uu____23862 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23862
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23908 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23908
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23954 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23954
                    then
                      let uu____23958 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23960 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23962 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23958 uu____23960 uu____23962
                    else ());
                   (let no_free_uvars t =
                      (let uu____23976 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23976) &&
                        (let uu____23980 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23980)
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
                      let uu____23997 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23997 = FStar_Syntax_Util.Equal  in
                    let uu____23998 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23998
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24002 = equal t1 t2  in
                         (if uu____24002
                          then
                            let uu____24005 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24005
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24010 =
                            let uu____24017 = equal t1 t2  in
                            if uu____24017
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24030 = mk_eq2 wl env orig t1 t2  in
                               match uu____24030 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24010 with
                          | (guard,wl1) ->
                              let uu____24051 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24051))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24054,uu____24055) ->
                  let head1 =
                    let uu____24057 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24057
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24103 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24103
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24149 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24149
                    then
                      let uu____24153 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24155 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24157 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24153 uu____24155 uu____24157
                    else ());
                   (let no_free_uvars t =
                      (let uu____24171 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24171) &&
                        (let uu____24175 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24175)
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
                      let uu____24192 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24192 = FStar_Syntax_Util.Equal  in
                    let uu____24193 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24193
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24197 = equal t1 t2  in
                         (if uu____24197
                          then
                            let uu____24200 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24200
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24205 =
                            let uu____24212 = equal t1 t2  in
                            if uu____24212
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24225 = mk_eq2 wl env orig t1 t2  in
                               match uu____24225 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24205 with
                          | (guard,wl1) ->
                              let uu____24246 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24246))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24249,uu____24250) ->
                  let head1 =
                    let uu____24252 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24252
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24298 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24298
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24344 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24344
                    then
                      let uu____24348 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24350 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24352 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24348 uu____24350 uu____24352
                    else ());
                   (let no_free_uvars t =
                      (let uu____24366 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24366) &&
                        (let uu____24370 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24370)
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
                      let uu____24387 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24387 = FStar_Syntax_Util.Equal  in
                    let uu____24388 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24388
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24392 = equal t1 t2  in
                         (if uu____24392
                          then
                            let uu____24395 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24395
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24400 =
                            let uu____24407 = equal t1 t2  in
                            if uu____24407
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24420 = mk_eq2 wl env orig t1 t2  in
                               match uu____24420 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24400 with
                          | (guard,wl1) ->
                              let uu____24441 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24441))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____24444,uu____24445) ->
                  let head1 =
                    let uu____24447 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24447
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24493 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24493
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24539 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24539
                    then
                      let uu____24543 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24545 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24547 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24543 uu____24545 uu____24547
                    else ());
                   (let no_free_uvars t =
                      (let uu____24561 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24561) &&
                        (let uu____24565 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24565)
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
                      let uu____24582 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24582 = FStar_Syntax_Util.Equal  in
                    let uu____24583 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24583
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24587 = equal t1 t2  in
                         (if uu____24587
                          then
                            let uu____24590 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24590
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24595 =
                            let uu____24602 = equal t1 t2  in
                            if uu____24602
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24615 = mk_eq2 wl env orig t1 t2  in
                               match uu____24615 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24595 with
                          | (guard,wl1) ->
                              let uu____24636 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24636))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____24639,uu____24640) ->
                  let head1 =
                    let uu____24658 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24658
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24704 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24704
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24750 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24750
                    then
                      let uu____24754 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24756 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24758 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24754 uu____24756 uu____24758
                    else ());
                   (let no_free_uvars t =
                      (let uu____24772 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24772) &&
                        (let uu____24776 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24776)
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
                      let uu____24793 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24793 = FStar_Syntax_Util.Equal  in
                    let uu____24794 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24794
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24798 = equal t1 t2  in
                         (if uu____24798
                          then
                            let uu____24801 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24801
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24806 =
                            let uu____24813 = equal t1 t2  in
                            if uu____24813
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24826 = mk_eq2 wl env orig t1 t2  in
                               match uu____24826 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24806 with
                          | (guard,wl1) ->
                              let uu____24847 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24847))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24850,FStar_Syntax_Syntax.Tm_match uu____24851) ->
                  let head1 =
                    let uu____24875 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24875
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24921 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24921
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24967 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24967
                    then
                      let uu____24971 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24973 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24975 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24971 uu____24973 uu____24975
                    else ());
                   (let no_free_uvars t =
                      (let uu____24989 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24989) &&
                        (let uu____24993 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24993)
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
                      let uu____25010 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25010 = FStar_Syntax_Util.Equal  in
                    let uu____25011 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25011
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25015 = equal t1 t2  in
                         (if uu____25015
                          then
                            let uu____25018 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25018
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25023 =
                            let uu____25030 = equal t1 t2  in
                            if uu____25030
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25043 = mk_eq2 wl env orig t1 t2  in
                               match uu____25043 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25023 with
                          | (guard,wl1) ->
                              let uu____25064 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25064))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25067,FStar_Syntax_Syntax.Tm_uinst uu____25068) ->
                  let head1 =
                    let uu____25076 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25076
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25116 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25116
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25156 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25156
                    then
                      let uu____25160 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25162 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25164 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25160 uu____25162 uu____25164
                    else ());
                   (let no_free_uvars t =
                      (let uu____25178 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25178) &&
                        (let uu____25182 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25182)
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
                      let uu____25199 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25199 = FStar_Syntax_Util.Equal  in
                    let uu____25200 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25200
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25204 = equal t1 t2  in
                         (if uu____25204
                          then
                            let uu____25207 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25207
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25212 =
                            let uu____25219 = equal t1 t2  in
                            if uu____25219
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25232 = mk_eq2 wl env orig t1 t2  in
                               match uu____25232 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25212 with
                          | (guard,wl1) ->
                              let uu____25253 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25253))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25256,FStar_Syntax_Syntax.Tm_name uu____25257) ->
                  let head1 =
                    let uu____25259 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25259
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25299 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25299
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25339 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25339
                    then
                      let uu____25343 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25345 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25347 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25343 uu____25345 uu____25347
                    else ());
                   (let no_free_uvars t =
                      (let uu____25361 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25361) &&
                        (let uu____25365 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25365)
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
                      let uu____25382 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25382 = FStar_Syntax_Util.Equal  in
                    let uu____25383 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25383
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25387 = equal t1 t2  in
                         (if uu____25387
                          then
                            let uu____25390 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25390
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25395 =
                            let uu____25402 = equal t1 t2  in
                            if uu____25402
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25415 = mk_eq2 wl env orig t1 t2  in
                               match uu____25415 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25395 with
                          | (guard,wl1) ->
                              let uu____25436 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25436))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25439,FStar_Syntax_Syntax.Tm_constant uu____25440) ->
                  let head1 =
                    let uu____25442 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25442
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25482 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25482
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25522 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25522
                    then
                      let uu____25526 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25528 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25530 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25526 uu____25528 uu____25530
                    else ());
                   (let no_free_uvars t =
                      (let uu____25544 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25544) &&
                        (let uu____25548 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25548)
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
                      let uu____25565 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25565 = FStar_Syntax_Util.Equal  in
                    let uu____25566 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25566
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25570 = equal t1 t2  in
                         (if uu____25570
                          then
                            let uu____25573 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25573
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25578 =
                            let uu____25585 = equal t1 t2  in
                            if uu____25585
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25598 = mk_eq2 wl env orig t1 t2  in
                               match uu____25598 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25578 with
                          | (guard,wl1) ->
                              let uu____25619 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25619))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25622,FStar_Syntax_Syntax.Tm_fvar uu____25623) ->
                  let head1 =
                    let uu____25625 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25625
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25665 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25665
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25705 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25705
                    then
                      let uu____25709 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25711 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25713 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25709 uu____25711 uu____25713
                    else ());
                   (let no_free_uvars t =
                      (let uu____25727 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25727) &&
                        (let uu____25731 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25731)
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
                      let uu____25748 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25748 = FStar_Syntax_Util.Equal  in
                    let uu____25749 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25749
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25753 = equal t1 t2  in
                         (if uu____25753
                          then
                            let uu____25756 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25756
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25761 =
                            let uu____25768 = equal t1 t2  in
                            if uu____25768
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25781 = mk_eq2 wl env orig t1 t2  in
                               match uu____25781 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25761 with
                          | (guard,wl1) ->
                              let uu____25802 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25802))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25805,FStar_Syntax_Syntax.Tm_app uu____25806) ->
                  let head1 =
                    let uu____25824 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25824
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25864 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25864
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25904 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25904
                    then
                      let uu____25908 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25910 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25912 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25908 uu____25910 uu____25912
                    else ());
                   (let no_free_uvars t =
                      (let uu____25926 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25926) &&
                        (let uu____25930 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25930)
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
                      let uu____25947 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25947 = FStar_Syntax_Util.Equal  in
                    let uu____25948 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25948
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25952 = equal t1 t2  in
                         (if uu____25952
                          then
                            let uu____25955 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25955
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25960 =
                            let uu____25967 = equal t1 t2  in
                            if uu____25967
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25980 = mk_eq2 wl env orig t1 t2  in
                               match uu____25980 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25960 with
                          | (guard,wl1) ->
                              let uu____26001 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26001))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26004,FStar_Syntax_Syntax.Tm_let uu____26005) ->
                  let uu____26032 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26032
                  then
                    let uu____26035 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26035
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____26039,uu____26040) ->
                  let uu____26054 =
                    let uu____26060 =
                      let uu____26062 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26064 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26066 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26068 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26062 uu____26064 uu____26066 uu____26068
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26060)
                     in
                  FStar_Errors.raise_error uu____26054
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26072,FStar_Syntax_Syntax.Tm_let uu____26073) ->
                  let uu____26087 =
                    let uu____26093 =
                      let uu____26095 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26097 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26099 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26101 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26095 uu____26097 uu____26099 uu____26101
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26093)
                     in
                  FStar_Errors.raise_error uu____26087
                    t1.FStar_Syntax_Syntax.pos
              | uu____26105 -> giveup env "head tag mismatch" orig))))

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
          (let uu____26169 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26169
           then
             let uu____26174 =
               let uu____26176 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26176  in
             let uu____26177 =
               let uu____26179 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26179  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26174 uu____26177
           else ());
          (let uu____26183 =
             let uu____26185 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26185  in
           if uu____26183
           then
             let uu____26188 =
               let uu____26190 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____26192 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____26190 uu____26192
                in
             giveup env uu____26188 orig
           else
             (let uu____26197 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____26197 with
              | (ret_sub_prob,wl1) ->
                  let uu____26205 =
                    FStar_List.fold_right2
                      (fun uu____26242  ->
                         fun uu____26243  ->
                           fun uu____26244  ->
                             match (uu____26242, uu____26243, uu____26244)
                             with
                             | ((a1,uu____26288),(a2,uu____26290),(arg_sub_probs,wl2))
                                 ->
                                 let uu____26323 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____26323 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____26205 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____26353 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____26353  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____26361 = attempt sub_probs wl3  in
                       solve env uu____26361)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____26384 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____26387)::[] -> wp1
              | uu____26412 ->
                  let uu____26423 =
                    let uu____26425 =
                      let uu____26427 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____26427  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____26425
                     in
                  failwith uu____26423
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____26434 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____26434]
              | x -> x  in
            let uu____26436 =
              let uu____26447 =
                let uu____26456 =
                  let uu____26457 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____26457 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____26456  in
              [uu____26447]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____26436;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____26475 = lift_c1 ()  in solve_eq uu____26475 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___353_26484  ->
                       match uu___353_26484 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____26489 -> false))
                in
             let uu____26491 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____26521)::uu____26522,(wp2,uu____26524)::uu____26525)
                   -> (wp1, wp2)
               | uu____26598 ->
                   let uu____26623 =
                     let uu____26629 =
                       let uu____26631 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____26633 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____26631 uu____26633
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____26629)
                      in
                   FStar_Errors.raise_error uu____26623
                     env.FStar_TypeChecker_Env.range
                in
             match uu____26491 with
             | (wpc1,wpc2) ->
                 let uu____26643 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____26643
                 then
                   let uu____26648 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____26648 wl
                 else
                   (let uu____26652 =
                      let uu____26659 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____26659  in
                    match uu____26652 with
                    | (c2_decl,qualifiers) ->
                        let uu____26680 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____26680
                        then
                          let c1_repr =
                            let uu____26687 =
                              let uu____26688 =
                                let uu____26689 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____26689  in
                              let uu____26690 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____26688 uu____26690
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____26687
                             in
                          let c2_repr =
                            let uu____26692 =
                              let uu____26693 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____26694 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____26693 uu____26694
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____26692
                             in
                          let uu____26695 =
                            let uu____26700 =
                              let uu____26702 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____26704 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____26702 uu____26704
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____26700
                             in
                          (match uu____26695 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____26710 = attempt [prob] wl2  in
                               solve env uu____26710)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____26725 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____26725
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____26734 =
                                     let uu____26741 =
                                       let uu____26742 =
                                         let uu____26759 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____26762 =
                                           let uu____26773 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____26782 =
                                             let uu____26793 =
                                               let uu____26802 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____26802
                                                in
                                             [uu____26793]  in
                                           uu____26773 :: uu____26782  in
                                         (uu____26759, uu____26762)  in
                                       FStar_Syntax_Syntax.Tm_app uu____26742
                                        in
                                     FStar_Syntax_Syntax.mk uu____26741  in
                                   uu____26734 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____26854 =
                                    let uu____26861 =
                                      let uu____26862 =
                                        let uu____26879 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____26882 =
                                          let uu____26893 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____26902 =
                                            let uu____26913 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____26922 =
                                              let uu____26933 =
                                                let uu____26942 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____26942
                                                 in
                                              [uu____26933]  in
                                            uu____26913 :: uu____26922  in
                                          uu____26893 :: uu____26902  in
                                        (uu____26879, uu____26882)  in
                                      FStar_Syntax_Syntax.Tm_app uu____26862
                                       in
                                    FStar_Syntax_Syntax.mk uu____26861  in
                                  uu____26854 FStar_Pervasives_Native.None r)
                              in
                           (let uu____26999 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____26999
                            then
                              let uu____27004 =
                                let uu____27006 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____27006
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____27004
                            else ());
                           (let uu____27010 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____27010 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____27019 =
                                    let uu____27022 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_12  ->
                                         FStar_Pervasives_Native.Some _0_12)
                                      uu____27022
                                     in
                                  solve_prob orig uu____27019 [] wl1  in
                                let uu____27025 = attempt [base_prob] wl2  in
                                solve env uu____27025))))
           in
        let uu____27026 = FStar_Util.physical_equality c1 c2  in
        if uu____27026
        then
          let uu____27029 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____27029
        else
          ((let uu____27033 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____27033
            then
              let uu____27038 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____27040 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____27038
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____27040
            else ());
           (let uu____27045 =
              let uu____27054 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____27057 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____27054, uu____27057)  in
            match uu____27045 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____27075),FStar_Syntax_Syntax.Total
                    (t2,uu____27077)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____27094 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____27094 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____27096,FStar_Syntax_Syntax.Total uu____27097) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____27116),FStar_Syntax_Syntax.Total
                    (t2,uu____27118)) ->
                     let uu____27135 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____27135 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____27138),FStar_Syntax_Syntax.GTotal
                    (t2,uu____27140)) ->
                     let uu____27157 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____27157 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____27160),FStar_Syntax_Syntax.GTotal
                    (t2,uu____27162)) ->
                     let uu____27179 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____27179 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____27181,FStar_Syntax_Syntax.Comp uu____27182) ->
                     let uu____27191 =
                       let uu___411_27194 = problem  in
                       let uu____27197 =
                         let uu____27198 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27198
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___411_27194.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____27197;
                         FStar_TypeChecker_Common.relation =
                           (uu___411_27194.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___411_27194.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___411_27194.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___411_27194.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___411_27194.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___411_27194.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___411_27194.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___411_27194.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____27191 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____27199,FStar_Syntax_Syntax.Comp uu____27200) ->
                     let uu____27209 =
                       let uu___411_27212 = problem  in
                       let uu____27215 =
                         let uu____27216 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27216
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___411_27212.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____27215;
                         FStar_TypeChecker_Common.relation =
                           (uu___411_27212.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___411_27212.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___411_27212.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___411_27212.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___411_27212.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___411_27212.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___411_27212.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___411_27212.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____27209 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____27217,FStar_Syntax_Syntax.GTotal uu____27218) ->
                     let uu____27227 =
                       let uu___412_27230 = problem  in
                       let uu____27233 =
                         let uu____27234 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27234
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___412_27230.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___412_27230.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___412_27230.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____27233;
                         FStar_TypeChecker_Common.element =
                           (uu___412_27230.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___412_27230.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___412_27230.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___412_27230.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___412_27230.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___412_27230.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____27227 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____27235,FStar_Syntax_Syntax.Total uu____27236) ->
                     let uu____27245 =
                       let uu___412_27248 = problem  in
                       let uu____27251 =
                         let uu____27252 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27252
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___412_27248.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___412_27248.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___412_27248.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____27251;
                         FStar_TypeChecker_Common.element =
                           (uu___412_27248.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___412_27248.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___412_27248.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___412_27248.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___412_27248.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___412_27248.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____27245 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____27253,FStar_Syntax_Syntax.Comp uu____27254) ->
                     let uu____27255 =
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
                     if uu____27255
                     then
                       let uu____27258 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____27258 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____27265 =
                            let uu____27270 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____27270
                            then (c1_comp, c2_comp)
                            else
                              (let uu____27279 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____27280 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____27279, uu____27280))
                             in
                          match uu____27265 with
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
                           (let uu____27288 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____27288
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____27296 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____27296 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____27299 =
                                  let uu____27301 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____27303 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____27301 uu____27303
                                   in
                                giveup env uu____27299 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____27314 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____27314 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____27364 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____27364 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____27389 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____27420  ->
                match uu____27420 with
                | (u1,u2) ->
                    let uu____27428 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____27430 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____27428 uu____27430))
         in
      FStar_All.pipe_right uu____27389 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____27467,[])) when
          let uu____27494 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____27494 -> "{}"
      | uu____27497 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____27524 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____27524
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____27536 =
              FStar_List.map
                (fun uu____27549  ->
                   match uu____27549 with
                   | (uu____27556,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____27536 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____27567 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____27567 imps
  
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
                  let uu____27624 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____27624
                  then
                    let uu____27632 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____27634 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____27632
                      (rel_to_string rel) uu____27634
                  else "TOP"  in
                let uu____27640 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____27640 with
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
              let uu____27700 =
                let uu____27703 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_13  -> FStar_Pervasives_Native.Some _0_13)
                  uu____27703
                 in
              FStar_Syntax_Syntax.new_bv uu____27700 t1  in
            let uu____27706 =
              let uu____27711 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____27711
               in
            match uu____27706 with | (p,wl1) -> (p, x, wl1)
  
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
            ((let uu____27789 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____27789
              then
                let uu____27796 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____27796
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
          ((let uu____27823 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____27823
            then
              let uu____27828 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____27828
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____27835 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____27835
             then
               let uu____27840 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____27840
             else ());
            (let f2 =
               let uu____27846 =
                 let uu____27847 = FStar_Syntax_Util.unmeta f1  in
                 uu____27847.FStar_Syntax_Syntax.n  in
               match uu____27846 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____27851 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___413_27852 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___413_27852.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___413_27852.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___413_27852.FStar_TypeChecker_Env.implicits)
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
            let uu____27907 =
              let uu____27908 =
                let uu____27909 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_14  -> FStar_TypeChecker_Common.NonTrivial _0_14)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____27909;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____27908  in
            FStar_All.pipe_left
              (fun _0_15  -> FStar_Pervasives_Native.Some _0_15) uu____27907
  
let with_guard_no_simp :
  'Auu____27925 .
    'Auu____27925 ->
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
            let uu____27948 =
              let uu____27949 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_16  -> FStar_TypeChecker_Common.NonTrivial _0_16)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____27949;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____27948
  
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
          (let uu____27982 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____27982
           then
             let uu____27987 = FStar_Syntax_Print.term_to_string t1  in
             let uu____27989 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____27987
               uu____27989
           else ());
          (let uu____27994 =
             let uu____27999 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____27999
              in
           match uu____27994 with
           | (prob,wl) ->
               let g =
                 let uu____28007 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____28017  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____28007  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____28053 = try_teq true env t1 t2  in
        match uu____28053 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____28058 = FStar_TypeChecker_Env.get_range env  in
              let uu____28059 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____28058 uu____28059);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____28067 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____28067
              then
                let uu____28072 = FStar_Syntax_Print.term_to_string t1  in
                let uu____28074 = FStar_Syntax_Print.term_to_string t2  in
                let uu____28076 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____28072
                  uu____28074 uu____28076
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
          let uu____28102 = FStar_TypeChecker_Env.get_range env  in
          let uu____28103 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____28102 uu____28103
  
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
        (let uu____28132 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____28132
         then
           let uu____28137 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____28139 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____28137 uu____28139
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____28150 =
           let uu____28157 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____28157 "sub_comp"
            in
         match uu____28150 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____28170 =
                 FStar_Util.record_time
                   (fun uu____28182  ->
                      let uu____28183 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____28194  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____28183)
                  in
               match uu____28170 with
               | (r,ms) ->
                   ((let uu____28225 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____28225
                     then
                       let uu____28230 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____28232 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____28234 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____28230 uu____28232
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____28234
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
      fun uu____28272  ->
        match uu____28272 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____28315 =
                 let uu____28321 =
                   let uu____28323 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____28325 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____28323 uu____28325
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____28321)  in
               let uu____28329 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____28315 uu____28329)
               in
            let equiv1 v1 v' =
              let uu____28342 =
                let uu____28347 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____28348 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____28347, uu____28348)  in
              match uu____28342 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____28368 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____28399 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____28399 with
                      | FStar_Syntax_Syntax.U_unif uu____28406 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____28435  ->
                                    match uu____28435 with
                                    | (u,v') ->
                                        let uu____28444 = equiv1 v1 v'  in
                                        if uu____28444
                                        then
                                          let uu____28449 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____28449 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____28470 -> []))
               in
            let uu____28475 =
              let wl =
                let uu___414_28479 = empty_worklist env  in
                {
                  attempting = (uu___414_28479.attempting);
                  wl_deferred = (uu___414_28479.wl_deferred);
                  ctr = (uu___414_28479.ctr);
                  defer_ok = false;
                  smt_ok = (uu___414_28479.smt_ok);
                  umax_heuristic_ok = (uu___414_28479.umax_heuristic_ok);
                  tcenv = (uu___414_28479.tcenv);
                  wl_implicits = (uu___414_28479.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____28498  ->
                      match uu____28498 with
                      | (lb,v1) ->
                          let uu____28505 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____28505 with
                           | USolved wl1 -> ()
                           | uu____28508 -> fail1 lb v1)))
               in
            let rec check_ineq uu____28519 =
              match uu____28519 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____28531) -> true
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
                      uu____28555,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____28557,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____28568) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____28576,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____28585 -> false)
               in
            let uu____28591 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____28608  ->
                      match uu____28608 with
                      | (u,v1) ->
                          let uu____28616 = check_ineq (u, v1)  in
                          if uu____28616
                          then true
                          else
                            ((let uu____28624 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____28624
                              then
                                let uu____28629 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____28631 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____28629
                                  uu____28631
                              else ());
                             false)))
               in
            if uu____28591
            then ()
            else
              ((let uu____28641 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____28641
                then
                  ((let uu____28647 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____28647);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____28659 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____28659))
                else ());
               (let uu____28672 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____28672))
  
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
        let fail1 uu____28746 =
          match uu____28746 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___415_28772 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___415_28772.attempting);
            wl_deferred = (uu___415_28772.wl_deferred);
            ctr = (uu___415_28772.ctr);
            defer_ok;
            smt_ok = (uu___415_28772.smt_ok);
            umax_heuristic_ok = (uu___415_28772.umax_heuristic_ok);
            tcenv = (uu___415_28772.tcenv);
            wl_implicits = (uu___415_28772.wl_implicits)
          }  in
        (let uu____28775 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____28775
         then
           let uu____28780 = FStar_Util.string_of_bool defer_ok  in
           let uu____28782 = wl_to_string wl  in
           let uu____28784 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____28780 uu____28782 uu____28784
         else ());
        (let g1 =
           let uu____28790 = solve_and_commit env wl fail1  in
           match uu____28790 with
           | FStar_Pervasives_Native.Some
               (uu____28797::uu____28798,uu____28799) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___416_28828 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___416_28828.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___416_28828.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____28829 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___417_28838 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___417_28838.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___417_28838.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___417_28838.FStar_TypeChecker_Env.implicits)
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
    let uu____28892 = FStar_ST.op_Bang last_proof_ns  in
    match uu____28892 with
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
            let uu___418_29017 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___418_29017.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___418_29017.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___418_29017.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____29018 =
            let uu____29020 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____29020  in
          if uu____29018
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____29032 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____29033 =
                       let uu____29035 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____29035
                        in
                     FStar_Errors.diag uu____29032 uu____29033)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____29043 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____29044 =
                        let uu____29046 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____29046
                         in
                      FStar_Errors.diag uu____29043 uu____29044)
                   else ();
                   (let uu____29052 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____29052
                      "discharge_guard'" env vc1);
                   (let uu____29054 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____29054 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____29063 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____29064 =
                                let uu____29066 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____29066
                                 in
                              FStar_Errors.diag uu____29063 uu____29064)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____29076 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____29077 =
                                let uu____29079 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____29079
                                 in
                              FStar_Errors.diag uu____29076 uu____29077)
                           else ();
                           (let vcs =
                              let uu____29093 = FStar_Options.use_tactics ()
                                 in
                              if uu____29093
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____29115  ->
                                     (let uu____29117 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____29117);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____29161  ->
                                              match uu____29161 with
                                              | (env1,goal,opts) ->
                                                  let uu____29177 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____29177, opts)))))
                              else
                                (let uu____29180 =
                                   let uu____29187 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____29187)  in
                                 [uu____29180])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____29220  ->
                                    match uu____29220 with
                                    | (env1,goal,opts) ->
                                        let uu____29230 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____29230 with
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
                                                (let uu____29242 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____29243 =
                                                   let uu____29245 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____29247 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____29245 uu____29247
                                                    in
                                                 FStar_Errors.diag
                                                   uu____29242 uu____29243)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____29254 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____29255 =
                                                   let uu____29257 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____29257
                                                    in
                                                 FStar_Errors.diag
                                                   uu____29254 uu____29255)
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
      let uu____29275 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____29275 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____29284 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____29284
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____29298 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____29298 with
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
        let uu____29328 = try_teq false env t1 t2  in
        match uu____29328 with
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
            let uu____29372 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____29372 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____29385 ->
                     let uu____29398 =
                       let uu____29399 = FStar_Syntax_Subst.compress r  in
                       uu____29399.FStar_Syntax_Syntax.n  in
                     (match uu____29398 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____29404) ->
                          unresolved ctx_u'
                      | uu____29421 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____29445 = acc  in
            match uu____29445 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____29464 = hd1  in
                     (match uu____29464 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____29475 = unresolved ctx_u  in
                             if uu____29475
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____29499 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____29499
                                     then
                                       let uu____29503 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____29503
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____29512 = teq_nosmt env1 t tm
                                          in
                                       match uu____29512 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Env.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___419_29522 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___419_29522.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___419_29522.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___419_29522.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___419_29522.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___419_29522.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___419_29522.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___419_29522.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___420_29530 = hd1  in
                                       {
                                         FStar_TypeChecker_Env.imp_reason =
                                           (uu___420_29530.FStar_TypeChecker_Env.imp_reason);
                                         FStar_TypeChecker_Env.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Env.imp_tm =
                                           (uu___420_29530.FStar_TypeChecker_Env.imp_tm);
                                         FStar_TypeChecker_Env.imp_range =
                                           (uu___420_29530.FStar_TypeChecker_Env.imp_range)
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
                                    let uu___421_29541 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___421_29541.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___421_29541.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___421_29541.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___421_29541.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___421_29541.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___421_29541.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___421_29541.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___421_29541.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___421_29541.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___421_29541.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___421_29541.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___421_29541.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___421_29541.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___421_29541.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___421_29541.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___421_29541.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___421_29541.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___421_29541.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___421_29541.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___421_29541.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___421_29541.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___421_29541.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___421_29541.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___421_29541.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___421_29541.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___421_29541.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___421_29541.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___421_29541.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___421_29541.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___421_29541.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___421_29541.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___421_29541.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___421_29541.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___421_29541.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___421_29541.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___421_29541.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___421_29541.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___421_29541.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___421_29541.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___421_29541.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___421_29541.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___421_29541.FStar_TypeChecker_Env.nbe)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___422_29545 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___422_29545.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___422_29545.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___422_29545.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___422_29545.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___422_29545.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___422_29545.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___422_29545.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___422_29545.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___422_29545.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___422_29545.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___422_29545.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___422_29545.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___422_29545.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___422_29545.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___422_29545.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___422_29545.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___422_29545.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___422_29545.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___422_29545.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___422_29545.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___422_29545.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___422_29545.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___422_29545.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___422_29545.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___422_29545.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___422_29545.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___422_29545.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___422_29545.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___422_29545.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___422_29545.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___422_29545.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___422_29545.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___422_29545.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___422_29545.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___422_29545.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___422_29545.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___422_29545.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___422_29545.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___422_29545.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___422_29545.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___422_29545.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___422_29545.FStar_TypeChecker_Env.nbe)
                                      }
                                    else env1  in
                                  (let uu____29550 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____29550
                                   then
                                     let uu____29555 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____29557 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____29559 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____29561 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____29555 uu____29557 uu____29559
                                       reason uu____29561
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___424_29568  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____29575 =
                                             let uu____29585 =
                                               let uu____29593 =
                                                 let uu____29595 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____29597 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____29599 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____29595 uu____29597
                                                   uu____29599
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____29593, r)
                                                in
                                             [uu____29585]  in
                                           FStar_Errors.add_errors
                                             uu____29575);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___425_29619 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___425_29619.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___425_29619.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___425_29619.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____29623 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____29634  ->
                                               let uu____29635 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____29637 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____29639 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____29635 uu____29637
                                                 reason uu____29639)) env2 g2
                                         true
                                        in
                                     match uu____29623 with
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
          let uu___426_29647 = g  in
          let uu____29648 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___426_29647.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___426_29647.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___426_29647.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____29648
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
        let uu____29691 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____29691 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____29692 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____29692
      | imp::uu____29694 ->
          let uu____29697 =
            let uu____29703 =
              let uu____29705 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____29707 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____29705 uu____29707 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____29703)
             in
          FStar_Errors.raise_error uu____29697
            imp.FStar_TypeChecker_Env.imp_range
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____29729 = teq_nosmt env t1 t2  in
        match uu____29729 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___427_29748 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___427_29748.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___427_29748.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___427_29748.FStar_TypeChecker_Env.implicits)
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
        (let uu____29784 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____29784
         then
           let uu____29789 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____29791 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____29789
             uu____29791
         else ());
        (let uu____29796 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____29796 with
         | (prob,x,wl) ->
             let g =
               let uu____29815 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____29826  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____29815  in
             ((let uu____29847 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____29847
               then
                 let uu____29852 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____29854 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____29856 =
                   let uu____29858 = FStar_Util.must g  in
                   guard_to_string env uu____29858  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____29852 uu____29854 uu____29856
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
        let uu____29895 = check_subtyping env t1 t2  in
        match uu____29895 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____29914 =
              let uu____29915 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____29915 g  in
            FStar_Pervasives_Native.Some uu____29914
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____29934 = check_subtyping env t1 t2  in
        match uu____29934 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____29953 =
              let uu____29954 =
                let uu____29955 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____29955]  in
              FStar_TypeChecker_Env.close_guard env uu____29954 g  in
            FStar_Pervasives_Native.Some uu____29953
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____29993 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____29993
         then
           let uu____29998 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____30000 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____29998
             uu____30000
         else ());
        (let uu____30005 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____30005 with
         | (prob,x,wl) ->
             let g =
               let uu____30020 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____30031  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30020  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____30055 =
                      let uu____30056 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____30056]  in
                    FStar_TypeChecker_Env.close_guard env uu____30055 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____30097 = subtype_nosmt env t1 t2  in
        match uu____30097 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  