open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____60279 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____60314 -> false
  
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
                    let uu____60737 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____60737;
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
                     (let uu___656_60769 = wl  in
                      {
                        attempting = (uu___656_60769.attempting);
                        wl_deferred = (uu___656_60769.wl_deferred);
                        ctr = (uu___656_60769.ctr);
                        defer_ok = (uu___656_60769.defer_ok);
                        smt_ok = (uu___656_60769.smt_ok);
                        umax_heuristic_ok =
                          (uu___656_60769.umax_heuristic_ok);
                        tcenv = (uu___656_60769.tcenv);
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
            let uu___662_60802 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___662_60802.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___662_60802.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___662_60802.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___662_60802.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___662_60802.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___662_60802.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___662_60802.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___662_60802.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___662_60802.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___662_60802.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___662_60802.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___662_60802.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___662_60802.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___662_60802.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___662_60802.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___662_60802.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___662_60802.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___662_60802.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___662_60802.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___662_60802.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___662_60802.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___662_60802.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___662_60802.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___662_60802.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___662_60802.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___662_60802.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___662_60802.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___662_60802.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___662_60802.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___662_60802.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___662_60802.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___662_60802.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___662_60802.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___662_60802.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___662_60802.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___662_60802.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___662_60802.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___662_60802.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___662_60802.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___662_60802.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___662_60802.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___662_60802.FStar_TypeChecker_Env.nbe)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____60804 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____60804 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Env.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * Prims.string) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____60847 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____60883 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * Prims.string)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____60916 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____60927 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____60938 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___585_60956  ->
    match uu___585_60956 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____60968 = FStar_Syntax_Util.head_and_args t  in
    match uu____60968 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____61031 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____61033 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____61048 =
                     let uu____61050 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____61050  in
                   FStar_Util.format1 "@<%s>" uu____61048
                in
             let uu____61054 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____61031 uu____61033 uu____61054
         | uu____61057 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___586_61069  ->
      match uu___586_61069 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____61074 =
            let uu____61078 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____61080 =
              let uu____61084 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____61086 =
                let uu____61090 =
                  let uu____61094 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____61094]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____61090
                 in
              uu____61084 :: uu____61086  in
            uu____61078 :: uu____61080  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____61074
      | FStar_TypeChecker_Common.CProb p ->
          let uu____61105 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____61107 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____61109 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____61105
            uu____61107 (rel_to_string p.FStar_TypeChecker_Common.relation)
            uu____61109
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___587_61123  ->
      match uu___587_61123 with
      | UNIV (u,t) ->
          let x =
            let uu____61129 = FStar_Options.hide_uvar_nums ()  in
            if uu____61129
            then "?"
            else
              (let uu____61136 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____61136 FStar_Util.string_of_int)
             in
          let uu____61140 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____61140
      | TERM (u,t) ->
          let x =
            let uu____61147 = FStar_Options.hide_uvar_nums ()  in
            if uu____61147
            then "?"
            else
              (let uu____61154 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____61154 FStar_Util.string_of_int)
             in
          let uu____61158 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____61158
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____61177 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____61177 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____61198 =
      let uu____61202 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____61202
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____61198 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____61221 .
    (FStar_Syntax_Syntax.term * 'Auu____61221) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____61240 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____61261  ->
              match uu____61261 with
              | (x,uu____61268) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____61240 (FStar_String.concat " ")
  
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
        (let uu____61311 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____61311
         then
           let uu____61316 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____61316
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___588_61327  ->
    match uu___588_61327 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____61333 .
    'Auu____61333 FStar_TypeChecker_Common.problem ->
      'Auu____61333 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___722_61345 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___722_61345.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___722_61345.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___722_61345.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___722_61345.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___722_61345.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___722_61345.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___722_61345.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____61353 .
    'Auu____61353 FStar_TypeChecker_Common.problem ->
      'Auu____61353 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___589_61373  ->
    match uu___589_61373 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _61379  -> FStar_TypeChecker_Common.TProb _61379)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _61385  -> FStar_TypeChecker_Common.CProb _61385)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___590_61391  ->
    match uu___590_61391 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___734_61397 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___734_61397.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___734_61397.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___734_61397.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___734_61397.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___734_61397.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___734_61397.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___734_61397.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___734_61397.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___734_61397.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___738_61405 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___738_61405.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___738_61405.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___738_61405.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___738_61405.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___738_61405.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___738_61405.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___738_61405.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___738_61405.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___738_61405.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___591_61418  ->
      match uu___591_61418 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___592_61425  ->
    match uu___592_61425 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___593_61438  ->
    match uu___593_61438 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___594_61453  ->
    match uu___594_61453 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___595_61468  ->
    match uu___595_61468 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___596_61482  ->
    match uu___596_61482 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___597_61496  ->
    match uu___597_61496 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___598_61508  ->
    match uu___598_61508 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____61524 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____61524) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____61554 =
          let uu____61556 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____61556  in
        if uu____61554
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____61593)::bs ->
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
          let uu____61640 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____61664 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____61664]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____61640
      | FStar_TypeChecker_Common.CProb p ->
          let uu____61692 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____61716 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____61716]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____61692
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____61763 =
          let uu____61765 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____61765  in
        if uu____61763
        then ()
        else
          (let uu____61770 =
             let uu____61773 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____61773
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____61770 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____61822 =
          let uu____61824 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____61824  in
        if uu____61822
        then ()
        else
          (let uu____61829 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____61829)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____61849 =
        let uu____61851 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____61851  in
      if uu____61849
      then ()
      else
        (let msgf m =
           let uu____61865 =
             let uu____61867 =
               let uu____61869 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____61869 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____61867  in
           Prims.op_Hat msg uu____61865  in
         (let uu____61874 = msgf "scope"  in
          let uu____61877 = p_scope prob  in
          def_scope_wf uu____61874 (p_loc prob) uu____61877);
         (let uu____61889 = msgf "guard"  in
          def_check_scoped uu____61889 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____61896 = msgf "lhs"  in
                def_check_scoped uu____61896 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____61899 = msgf "rhs"  in
                def_check_scoped uu____61899 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____61906 = msgf "lhs"  in
                def_check_scoped_comp uu____61906 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____61909 = msgf "rhs"  in
                def_check_scoped_comp uu____61909 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___831_61930 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___831_61930.wl_deferred);
          ctr = (uu___831_61930.ctr);
          defer_ok = (uu___831_61930.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___831_61930.umax_heuristic_ok);
          tcenv = (uu___831_61930.tcenv);
          wl_implicits = (uu___831_61930.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____61938 .
    FStar_TypeChecker_Env.env ->
      ('Auu____61938 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___835_61961 = empty_worklist env  in
      let uu____61962 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____61962;
        wl_deferred = (uu___835_61961.wl_deferred);
        ctr = (uu___835_61961.ctr);
        defer_ok = (uu___835_61961.defer_ok);
        smt_ok = (uu___835_61961.smt_ok);
        umax_heuristic_ok = (uu___835_61961.umax_heuristic_ok);
        tcenv = (uu___835_61961.tcenv);
        wl_implicits = (uu___835_61961.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___840_61985 = wl  in
        {
          attempting = (uu___840_61985.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___840_61985.ctr);
          defer_ok = (uu___840_61985.defer_ok);
          smt_ok = (uu___840_61985.smt_ok);
          umax_heuristic_ok = (uu___840_61985.umax_heuristic_ok);
          tcenv = (uu___840_61985.tcenv);
          wl_implicits = (uu___840_61985.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___845_62013 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___845_62013.wl_deferred);
         ctr = (uu___845_62013.ctr);
         defer_ok = (uu___845_62013.defer_ok);
         smt_ok = (uu___845_62013.smt_ok);
         umax_heuristic_ok = (uu___845_62013.umax_heuristic_ok);
         tcenv = (uu___845_62013.tcenv);
         wl_implicits = (uu___845_62013.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____62027 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____62027 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____62061 = FStar_Syntax_Util.type_u ()  in
            match uu____62061 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____62073 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____62073 with
                 | (uu____62091,tt,wl1) ->
                     let uu____62094 = FStar_Syntax_Util.mk_eq2 u tt t1 t2
                        in
                     (uu____62094, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___599_62100  ->
    match uu___599_62100 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _62106  -> FStar_TypeChecker_Common.TProb _62106) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _62112  -> FStar_TypeChecker_Common.CProb _62112) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____62120 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____62120 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____62140  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____62182 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____62182 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____62182 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____62182 FStar_TypeChecker_Common.problem *
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
                        let uu____62269 =
                          let uu____62278 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____62278]  in
                        FStar_List.append scope uu____62269
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____62321 =
                      let uu____62324 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____62324  in
                    FStar_List.append uu____62321
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____62343 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____62343 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____62369 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____62369;
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
                  (let uu____62443 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____62443 with
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
                  (let uu____62531 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____62531 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____62569 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____62569 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____62569 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____62569 FStar_TypeChecker_Common.problem *
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
                          let uu____62637 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____62637]  in
                        let uu____62656 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____62656
                     in
                  let uu____62659 =
                    let uu____62666 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___928_62677 = wl  in
                       {
                         attempting = (uu___928_62677.attempting);
                         wl_deferred = (uu___928_62677.wl_deferred);
                         ctr = (uu___928_62677.ctr);
                         defer_ok = (uu___928_62677.defer_ok);
                         smt_ok = (uu___928_62677.smt_ok);
                         umax_heuristic_ok =
                           (uu___928_62677.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___928_62677.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____62666
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____62659 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____62695 =
                              let uu____62700 =
                                let uu____62701 =
                                  let uu____62710 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____62710
                                   in
                                [uu____62701]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____62700
                               in
                            uu____62695 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____62738 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____62738;
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
                let uu____62786 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____62786;
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
  'Auu____62801 .
    worklist ->
      'Auu____62801 FStar_TypeChecker_Common.problem ->
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
              let uu____62834 =
                let uu____62837 =
                  let uu____62838 =
                    let uu____62845 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____62845)  in
                  FStar_Syntax_Syntax.NT uu____62838  in
                [uu____62837]  in
              FStar_Syntax_Subst.subst uu____62834 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____62869 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____62869
        then
          let uu____62877 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____62880 = prob_to_string env d  in
          let uu____62882 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____62877 uu____62880 uu____62882 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____62898 -> failwith "impossible"  in
           let uu____62901 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____62917 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____62919 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____62917, uu____62919)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____62926 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____62928 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____62926, uu____62928)
              in
           match uu____62901 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___600_62956  ->
            match uu___600_62956 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____62968 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____62972 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____62972 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___601_63003  ->
           match uu___601_63003 with
           | UNIV uu____63006 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____63013 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____63013
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
        (fun uu___602_63041  ->
           match uu___602_63041 with
           | UNIV (u',t) ->
               let uu____63046 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____63046
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____63053 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____63065 =
        let uu____63066 =
          let uu____63067 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____63067
           in
        FStar_Syntax_Subst.compress uu____63066  in
      FStar_All.pipe_right uu____63065 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____63079 =
        let uu____63080 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____63080  in
      FStar_All.pipe_right uu____63079 FStar_Syntax_Util.unlazy_emb
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____63088 = FStar_Syntax_Util.head_and_args t  in
    match uu____63088 with
    | (h,uu____63107) ->
        let uu____63132 =
          let uu____63133 = FStar_Syntax_Subst.compress h  in
          uu____63133.FStar_Syntax_Syntax.n  in
        (match uu____63132 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____63138 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____63151 = should_strongly_reduce t  in
      if uu____63151
      then
        let uu____63154 =
          let uu____63155 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Reify;
              FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant] env t
             in
          FStar_Syntax_Subst.compress uu____63155  in
        FStar_All.pipe_right uu____63154 FStar_Syntax_Util.unlazy_emb
      else whnf' env t
  
let norm_arg :
  'Auu____63165 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____63165) ->
        (FStar_Syntax_Syntax.term * 'Auu____63165)
  =
  fun env  ->
    fun t  ->
      let uu____63188 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____63188, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____63240  ->
              match uu____63240 with
              | (x,imp) ->
                  let uu____63259 =
                    let uu___1025_63260 = x  in
                    let uu____63261 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1025_63260.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1025_63260.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____63261
                    }  in
                  (uu____63259, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____63285 = aux u3  in
            FStar_Syntax_Syntax.U_succ uu____63285
        | FStar_Syntax_Syntax.U_max us ->
            let uu____63289 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____63289
        | uu____63292 -> u2  in
      let uu____63293 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____63293
  
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
                (let uu____63414 = norm_refinement env t12  in
                 match uu____63414 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____63429;
                     FStar_Syntax_Syntax.vars = uu____63430;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____63454 =
                       let uu____63456 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____63458 = FStar_Syntax_Print.tag_of_term tt
                          in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____63456 uu____63458
                        in
                     failwith uu____63454)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____63474 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____63474
          | FStar_Syntax_Syntax.Tm_uinst uu____63475 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____63512 =
                   let uu____63513 = FStar_Syntax_Subst.compress t1'  in
                   uu____63513.FStar_Syntax_Syntax.n  in
                 match uu____63512 with
                 | FStar_Syntax_Syntax.Tm_refine uu____63528 -> aux true t1'
                 | uu____63536 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____63551 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____63582 =
                   let uu____63583 = FStar_Syntax_Subst.compress t1'  in
                   uu____63583.FStar_Syntax_Syntax.n  in
                 match uu____63582 with
                 | FStar_Syntax_Syntax.Tm_refine uu____63598 -> aux true t1'
                 | uu____63606 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____63621 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____63668 =
                   let uu____63669 = FStar_Syntax_Subst.compress t1'  in
                   uu____63669.FStar_Syntax_Syntax.n  in
                 match uu____63668 with
                 | FStar_Syntax_Syntax.Tm_refine uu____63684 -> aux true t1'
                 | uu____63692 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____63707 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____63722 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____63737 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____63752 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____63767 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____63796 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____63829 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____63850 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____63877 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____63905 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____63942 ->
              let uu____63949 =
                let uu____63951 = FStar_Syntax_Print.term_to_string t12  in
                let uu____63953 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____63951 uu____63953
                 in
              failwith uu____63949
          | FStar_Syntax_Syntax.Tm_ascribed uu____63968 ->
              let uu____63995 =
                let uu____63997 = FStar_Syntax_Print.term_to_string t12  in
                let uu____63999 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____63997 uu____63999
                 in
              failwith uu____63995
          | FStar_Syntax_Syntax.Tm_delayed uu____64014 ->
              let uu____64037 =
                let uu____64039 = FStar_Syntax_Print.term_to_string t12  in
                let uu____64041 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____64039 uu____64041
                 in
              failwith uu____64037
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____64056 =
                let uu____64058 = FStar_Syntax_Print.term_to_string t12  in
                let uu____64060 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____64058 uu____64060
                 in
              failwith uu____64056
           in
        let uu____64075 = whnf env t1  in aux false uu____64075
  
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
      let uu____64136 = base_and_refinement env t  in
      FStar_All.pipe_right uu____64136 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____64177 = FStar_Syntax_Syntax.null_bv t  in
    (uu____64177, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____64204 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____64204 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____64264  ->
    match uu____64264 with
    | (t_base,refopt) ->
        let uu____64295 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____64295 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____64337 =
      let uu____64341 =
        let uu____64344 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____64371  ->
                  match uu____64371 with | (uu____64380,uu____64381,x) -> x))
           in
        FStar_List.append wl.attempting uu____64344  in
      FStar_List.map (wl_prob_to_string wl) uu____64341  in
    FStar_All.pipe_right uu____64337 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____64404 .
    ('Auu____64404 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____64416  ->
    match uu____64416 with
    | (uu____64423,c,args) ->
        let uu____64426 = print_ctx_uvar c  in
        let uu____64428 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____64426 uu____64428
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____64438 = FStar_Syntax_Util.head_and_args t  in
    match uu____64438 with
    | (head1,_args) ->
        let uu____64482 =
          let uu____64483 = FStar_Syntax_Subst.compress head1  in
          uu____64483.FStar_Syntax_Syntax.n  in
        (match uu____64482 with
         | FStar_Syntax_Syntax.Tm_uvar uu____64487 -> true
         | uu____64501 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____64509 = FStar_Syntax_Util.head_and_args t  in
    match uu____64509 with
    | (head1,_args) ->
        let uu____64552 =
          let uu____64553 = FStar_Syntax_Subst.compress head1  in
          uu____64553.FStar_Syntax_Syntax.n  in
        (match uu____64552 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____64557) -> u
         | uu____64574 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____64599 = FStar_Syntax_Util.head_and_args t  in
      match uu____64599 with
      | (head1,args) ->
          let uu____64646 =
            let uu____64647 = FStar_Syntax_Subst.compress head1  in
            uu____64647.FStar_Syntax_Syntax.n  in
          (match uu____64646 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____64655)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____64688 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___603_64713  ->
                         match uu___603_64713 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____64718 =
                               let uu____64719 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____64719.FStar_Syntax_Syntax.n  in
                             (match uu____64718 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____64724 -> false)
                         | uu____64726 -> true))
                  in
               (match uu____64688 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____64751 =
                        FStar_List.collect
                          (fun uu___604_64763  ->
                             match uu___604_64763 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____64767 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____64767]
                             | uu____64768 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____64751 FStar_List.rev  in
                    let uu____64791 =
                      let uu____64798 =
                        let uu____64807 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___605_64829  ->
                                  match uu___605_64829 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____64833 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____64833]
                                  | uu____64834 -> []))
                           in
                        FStar_All.pipe_right uu____64807 FStar_List.rev  in
                      let uu____64857 =
                        let uu____64860 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____64860  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____64798 uu____64857
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____64791 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____64896  ->
                                match uu____64896 with
                                | (x,i) ->
                                    let uu____64915 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____64915, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____64946  ->
                                match uu____64946 with
                                | (a,i) ->
                                    let uu____64965 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____64965, i)) args_sol
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
           | uu____64987 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____65009 =
          let uu____65032 =
            let uu____65033 = FStar_Syntax_Subst.compress k  in
            uu____65033.FStar_Syntax_Syntax.n  in
          match uu____65032 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____65115 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____65115)
              else
                (let uu____65150 = FStar_Syntax_Util.abs_formals t  in
                 match uu____65150 with
                 | (ys',t1,uu____65183) ->
                     let uu____65188 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____65188))
          | uu____65227 ->
              let uu____65228 =
                let uu____65233 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____65233)  in
              ((ys, t), uu____65228)
           in
        match uu____65009 with
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
                 let uu____65328 = FStar_Syntax_Util.rename_binders xs ys1
                    in
                 FStar_Syntax_Subst.subst_comp uu____65328 c  in
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
               (let uu____65406 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____65406
                then
                  let uu____65411 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____65413 = print_ctx_uvar uv  in
                  let uu____65415 = FStar_Syntax_Print.term_to_string phi1
                     in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____65411 uu____65413 uu____65415
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____65424 =
                   let uu____65426 = FStar_Util.string_of_int (p_pid prob)
                      in
                   Prims.op_Hat "solve_prob'.sol." uu____65426  in
                 let uu____65429 =
                   let uu____65432 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____65432
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____65424 uu____65429 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____65465 =
               let uu____65466 =
                 let uu____65468 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____65470 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____65468 uu____65470
                  in
               failwith uu____65466  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____65536  ->
                       match uu____65536 with
                       | (a,i) ->
                           let uu____65557 =
                             let uu____65558 = FStar_Syntax_Subst.compress a
                                in
                             uu____65558.FStar_Syntax_Syntax.n  in
                           (match uu____65557 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____65584 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____65594 =
                 let uu____65596 = is_flex g  in
                 Prims.op_Negation uu____65596  in
               if uu____65594
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____65605 = destruct_flex_t g wl  in
                  match uu____65605 with
                  | ((uu____65610,uv1,args),wl1) ->
                      ((let uu____65615 = args_as_binders args  in
                        assign_solution uu____65615 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___1277_65617 = wl1  in
              {
                attempting = (uu___1277_65617.attempting);
                wl_deferred = (uu___1277_65617.wl_deferred);
                ctr = (wl1.ctr + (Prims.parse_int "1"));
                defer_ok = (uu___1277_65617.defer_ok);
                smt_ok = (uu___1277_65617.smt_ok);
                umax_heuristic_ok = (uu___1277_65617.umax_heuristic_ok);
                tcenv = (uu___1277_65617.tcenv);
                wl_implicits = (uu___1277_65617.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____65642 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____65642
         then
           let uu____65647 = FStar_Util.string_of_int pid  in
           let uu____65649 =
             let uu____65651 = FStar_List.map (uvi_to_string wl.tcenv) sol
                in
             FStar_All.pipe_right uu____65651 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____65647
             uu____65649
         else ());
        commit sol;
        (let uu___1285_65665 = wl  in
         {
           attempting = (uu___1285_65665.attempting);
           wl_deferred = (uu___1285_65665.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___1285_65665.defer_ok);
           smt_ok = (uu___1285_65665.smt_ok);
           umax_heuristic_ok = (uu___1285_65665.umax_heuristic_ok);
           tcenv = (uu___1285_65665.tcenv);
           wl_implicits = (uu___1285_65665.wl_implicits)
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
             | (uu____65731,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____65759 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____65759
              in
           (let uu____65765 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____65765
            then
              let uu____65770 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____65774 =
                let uu____65776 =
                  FStar_List.map (uvi_to_string wl.tcenv) uvis  in
                FStar_All.pipe_right uu____65776 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____65770
                uu____65774
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
        let uu____65811 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____65811 FStar_Util.set_elements  in
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
      let uu____65851 = occurs uk t  in
      match uu____65851 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____65890 =
                 let uu____65892 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____65894 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____65892 uu____65894
                  in
               FStar_Pervasives_Native.Some uu____65890)
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
            let uu____66014 = maximal_prefix bs_tail bs'_tail  in
            (match uu____66014 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____66065 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____66122  ->
             match uu____66122 with
             | (x,uu____66134) -> (FStar_Syntax_Syntax.Binding_var x) :: g1)
        g bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____66152 = FStar_List.last bs  in
      match uu____66152 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____66176) ->
          let uu____66187 =
            FStar_Util.prefix_until
              (fun uu___606_66202  ->
                 match uu___606_66202 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____66205 -> false) g
             in
          (match uu____66187 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____66219,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____66256 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____66256 with
        | (pfx,uu____66266) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____66278 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____66278 with
             | (uu____66286,src',wl1) ->
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
                 | uu____66400 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____66401 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____66465  ->
                  fun uu____66466  ->
                    match (uu____66465, uu____66466) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____66569 =
                          let uu____66571 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____66571
                           in
                        if uu____66569
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____66605 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____66605
                           then
                             let uu____66622 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____66622)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____66401 with | (isect,uu____66672) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____66708 'Auu____66709 .
    (FStar_Syntax_Syntax.bv * 'Auu____66708) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____66709) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____66767  ->
              fun uu____66768  ->
                match (uu____66767, uu____66768) with
                | ((a,uu____66787),(b,uu____66789)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____66805 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____66805) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____66836  ->
           match uu____66836 with
           | (y,uu____66843) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____66853 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____66853) Prims.list ->
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
                   let uu____67015 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____67015
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____67048 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____67100 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____67144 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____67165 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___607_67173  ->
    match uu___607_67173 with
    | MisMatch (d1,d2) ->
        let uu____67185 =
          let uu____67187 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____67189 =
            let uu____67191 =
              let uu____67193 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____67193 ")"  in
            Prims.op_Hat ") (" uu____67191  in
          Prims.op_Hat uu____67187 uu____67189  in
        Prims.op_Hat "MisMatch (" uu____67185
    | HeadMatch u ->
        let uu____67200 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____67200
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___608_67209  ->
    match uu___608_67209 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____67226 -> HeadMatch false
  
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
          let uu____67248 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____67248 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____67259 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____67283 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____67293 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____67320 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____67320
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____67321 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____67322 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____67323 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____67336 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____67350 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____67374) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____67380,uu____67381) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____67423) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____67448;
             FStar_Syntax_Syntax.index = uu____67449;
             FStar_Syntax_Syntax.sort = t2;_},uu____67451)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____67459 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____67460 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____67461 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____67476 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____67483 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____67503 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____67503
  
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
           { FStar_Syntax_Syntax.blob = uu____67522;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____67523;
             FStar_Syntax_Syntax.ltyp = uu____67524;
             FStar_Syntax_Syntax.rng = uu____67525;_},uu____67526)
            ->
            let uu____67537 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____67537 t21
        | (uu____67538,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____67539;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____67540;
             FStar_Syntax_Syntax.ltyp = uu____67541;
             FStar_Syntax_Syntax.rng = uu____67542;_})
            ->
            let uu____67553 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____67553
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____67565 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____67565
            then FullMatch
            else
              (let uu____67570 =
                 let uu____67579 =
                   let uu____67582 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____67582  in
                 let uu____67583 =
                   let uu____67586 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____67586  in
                 (uu____67579, uu____67583)  in
               MisMatch uu____67570)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____67592),FStar_Syntax_Syntax.Tm_uinst (g,uu____67594)) ->
            let uu____67603 = head_matches env f g  in
            FStar_All.pipe_right uu____67603 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____67604) -> HeadMatch true
        | (uu____67606,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____67610 = FStar_Const.eq_const c d  in
            if uu____67610
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____67620),FStar_Syntax_Syntax.Tm_uvar (uv',uu____67622)) ->
            let uu____67655 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____67655
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____67665),FStar_Syntax_Syntax.Tm_refine (y,uu____67667)) ->
            let uu____67676 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____67676 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____67678),uu____67679) ->
            let uu____67684 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____67684 head_match
        | (uu____67685,FStar_Syntax_Syntax.Tm_refine (x,uu____67687)) ->
            let uu____67692 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____67692 head_match
        | (FStar_Syntax_Syntax.Tm_type
           uu____67693,FStar_Syntax_Syntax.Tm_type uu____67694) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____67696,FStar_Syntax_Syntax.Tm_arrow uu____67697) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____67728),FStar_Syntax_Syntax.Tm_app
           (head',uu____67730)) ->
            let uu____67779 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____67779 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____67781),uu____67782) ->
            let uu____67807 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____67807 head_match
        | (uu____67808,FStar_Syntax_Syntax.Tm_app (head1,uu____67810)) ->
            let uu____67835 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____67835 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____67836,FStar_Syntax_Syntax.Tm_let
           uu____67837) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____67865,FStar_Syntax_Syntax.Tm_match uu____67866) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____67912,FStar_Syntax_Syntax.Tm_abs
           uu____67913) -> HeadMatch true
        | uu____67951 ->
            let uu____67956 =
              let uu____67965 = delta_depth_of_term env t11  in
              let uu____67968 = delta_depth_of_term env t21  in
              (uu____67965, uu____67968)  in
            MisMatch uu____67956
  
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
            (let uu____68034 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____68034
             then
               let uu____68039 = FStar_Syntax_Print.term_to_string t  in
               let uu____68041 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____68039 uu____68041
             else ());
            (let uu____68046 =
               let uu____68047 = FStar_Syntax_Util.un_uinst head1  in
               uu____68047.FStar_Syntax_Syntax.n  in
             match uu____68046 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____68053 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____68053 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____68067 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____68067
                        then
                          let uu____68072 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____68072
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____68077 ->
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
                      let uu____68094 =
                        let uu____68096 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____68096 = FStar_Syntax_Util.Equal  in
                      if uu____68094
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____68103 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____68103
                          then
                            let uu____68108 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____68110 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n"
                              uu____68108 uu____68110
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____68115 -> FStar_Pervasives_Native.None)
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
            (let uu____68267 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____68267
             then
               let uu____68272 = FStar_Syntax_Print.term_to_string t11  in
               let uu____68274 = FStar_Syntax_Print.term_to_string t21  in
               let uu____68276 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____68272
                 uu____68274 uu____68276
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____68304 =
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
               match uu____68304 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____68352 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____68352 with
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
                  uu____68390),uu____68391)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____68412 =
                      let uu____68421 = maybe_inline t11  in
                      let uu____68424 = maybe_inline t21  in
                      (uu____68421, uu____68424)  in
                    match uu____68412 with
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
                 (uu____68467,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  uu____68468))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____68489 =
                      let uu____68498 = maybe_inline t11  in
                      let uu____68501 = maybe_inline t21  in
                      (uu____68498, uu____68501)  in
                    match uu____68489 with
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
             | MisMatch uu____68556 -> fail1 n_delta r t11 t21
             | uu____68565 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____68580 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____68580
           then
             let uu____68585 = FStar_Syntax_Print.term_to_string t1  in
             let uu____68587 = FStar_Syntax_Print.term_to_string t2  in
             let uu____68589 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____68597 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____68614 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____68614
                    (fun uu____68649  ->
                       match uu____68649 with
                       | (t11,t21) ->
                           let uu____68657 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____68659 =
                             let uu____68661 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____68661  in
                           Prims.op_Hat uu____68657 uu____68659))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____68585 uu____68587 uu____68589 uu____68597
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____68678 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____68678 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___609_68693  ->
    match uu___609_68693 with
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
      let uu___1789_68742 = p  in
      let uu____68745 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____68746 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1789_68742.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____68745;
        FStar_TypeChecker_Common.relation =
          (uu___1789_68742.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____68746;
        FStar_TypeChecker_Common.element =
          (uu___1789_68742.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1789_68742.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1789_68742.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1789_68742.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1789_68742.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1789_68742.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____68761 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____68761
            (fun _68766  -> FStar_TypeChecker_Common.TProb _68766)
      | FStar_TypeChecker_Common.CProb uu____68767 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____68790 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____68790 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____68798 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____68798 with
           | (lh,lhs_args) ->
               let uu____68845 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____68845 with
                | (rh,rhs_args) ->
                    let uu____68892 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____68905,FStar_Syntax_Syntax.Tm_uvar uu____68906)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____68995 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____69022,uu____69023)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____69038,FStar_Syntax_Syntax.Tm_uvar uu____69039)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____69054,FStar_Syntax_Syntax.Tm_arrow
                         uu____69055) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_69085 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_69085.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_69085.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_69085.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_69085.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_69085.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_69085.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_69085.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_69085.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_69085.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____69088,FStar_Syntax_Syntax.Tm_type uu____69089)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_69105 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_69105.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_69105.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_69105.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_69105.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_69105.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_69105.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_69105.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_69105.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_69105.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____69108,FStar_Syntax_Syntax.Tm_uvar uu____69109)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_69125 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_69125.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_69125.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_69125.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_69125.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_69125.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_69125.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_69125.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_69125.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_69125.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____69128,FStar_Syntax_Syntax.Tm_uvar uu____69129)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____69144,uu____69145)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____69160,FStar_Syntax_Syntax.Tm_uvar uu____69161)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____69176,uu____69177) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____68892 with
                     | (rank,tp1) ->
                         let uu____69190 =
                           FStar_All.pipe_right
                             (let uu___1860_69194 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1860_69194.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1860_69194.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1860_69194.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1860_69194.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1860_69194.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1860_69194.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1860_69194.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1860_69194.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1860_69194.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _69197  ->
                                FStar_TypeChecker_Common.TProb _69197)
                            in
                         (rank, uu____69190))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____69201 =
            FStar_All.pipe_right
              (let uu___1864_69205 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1864_69205.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1864_69205.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1864_69205.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1864_69205.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1864_69205.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1864_69205.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1864_69205.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1864_69205.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1864_69205.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _69208  -> FStar_TypeChecker_Common.CProb _69208)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____69201)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____69268 probs =
      match uu____69268 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____69349 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____69370 = rank wl.tcenv hd1  in
               (match uu____69370 with
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
                      (let uu____69431 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____69436 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____69436)
                          in
                       if uu____69431
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
          let uu____69509 = FStar_Syntax_Util.head_and_args t  in
          match uu____69509 with
          | (hd1,uu____69528) ->
              let uu____69553 =
                let uu____69554 = FStar_Syntax_Subst.compress hd1  in
                uu____69554.FStar_Syntax_Syntax.n  in
              (match uu____69553 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____69559) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____69594  ->
                           match uu____69594 with
                           | (y,uu____69603) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____69626  ->
                                       match uu____69626 with
                                       | (x,uu____69635) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____69640 -> false)
           in
        let uu____69642 = rank tcenv p  in
        match uu____69642 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____69651 -> true
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
    match projectee with | UDeferred _0 -> true | uu____69688 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____69707 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____69727 -> false
  
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
                        let uu____69789 = FStar_Syntax_Util.univ_kernel u3
                           in
                        match uu____69789 with
                        | (k,uu____69797) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____69810 -> false)))
            | uu____69812 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____69864 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____69872 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____69872 = (Prims.parse_int "0")))
                           in
                        if uu____69864 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____69893 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____69901 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____69901 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____69893)
               in
            let uu____69905 = filter1 u12  in
            let uu____69908 = filter1 u22  in (uu____69905, uu____69908)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then UFailed "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____69943 = filter_out_common_univs us1 us2  in
                   (match uu____69943 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____70003 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____70003 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____70006 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          (let uu____70017 =
                             let uu____70019 =
                               FStar_Syntax_Print.univ_to_string u12  in
                             let uu____70021 =
                               FStar_Syntax_Print.univ_to_string u22  in
                             FStar_Util.format2
                               "Unable to unify universes: %s and %s"
                               uu____70019 uu____70021
                              in
                           UFailed uu____70017))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____70047 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____70047 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____70073 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____70073 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____70076 ->
                   let uu____70081 =
                     let uu____70083 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____70085 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format3
                       "Unable to unify universes: %s and %s (%s)"
                       uu____70083 uu____70085 msg
                      in
                   UFailed uu____70081)
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____70088,uu____70089) ->
              let uu____70091 =
                let uu____70093 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____70095 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____70093 uu____70095
                 in
              failwith uu____70091
          | (FStar_Syntax_Syntax.U_unknown ,uu____70098) ->
              let uu____70099 =
                let uu____70101 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____70103 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____70101 uu____70103
                 in
              failwith uu____70099
          | (uu____70106,FStar_Syntax_Syntax.U_bvar uu____70107) ->
              let uu____70109 =
                let uu____70111 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____70113 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____70111 uu____70113
                 in
              failwith uu____70109
          | (uu____70116,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____70117 =
                let uu____70119 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____70121 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____70119 uu____70121
                 in
              failwith uu____70117
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____70151 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____70151
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____70168 = occurs_univ v1 u3  in
              if uu____70168
              then
                let uu____70171 =
                  let uu____70173 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____70175 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____70173 uu____70175
                   in
                try_umax_components u11 u21 uu____70171
              else
                (let uu____70180 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____70180)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____70192 = occurs_univ v1 u3  in
              if uu____70192
              then
                let uu____70195 =
                  let uu____70197 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____70199 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____70197 uu____70199
                   in
                try_umax_components u11 u21 uu____70195
              else
                (let uu____70204 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____70204)
          | (FStar_Syntax_Syntax.U_max uu____70205,uu____70206) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____70214 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____70214
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____70220,FStar_Syntax_Syntax.U_max uu____70221) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____70229 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____70229
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____70235,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____70237,FStar_Syntax_Syntax.U_name uu____70238) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____70240) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____70242) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____70244,FStar_Syntax_Syntax.U_succ uu____70245) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____70247,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____70354 = bc1  in
      match uu____70354 with
      | (bs1,mk_cod1) ->
          let uu____70398 = bc2  in
          (match uu____70398 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____70509 = aux xs ys  in
                     (match uu____70509 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____70592 =
                       let uu____70599 = mk_cod1 xs  in ([], uu____70599)  in
                     let uu____70602 =
                       let uu____70609 = mk_cod2 ys  in ([], uu____70609)  in
                     (uu____70592, uu____70602)
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
                  let uu____70678 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____70678 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____70681 =
                    let uu____70682 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____70682 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____70681
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____70687 = has_type_guard t1 t2  in (uu____70687, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____70688 = has_type_guard t2 t1  in (uu____70688, wl)
  
let is_flex_pat :
  'Auu____70698 'Auu____70699 'Auu____70700 .
    ('Auu____70698 * 'Auu____70699 * 'Auu____70700 Prims.list) -> Prims.bool
  =
  fun uu___610_70714  ->
    match uu___610_70714 with
    | (uu____70723,uu____70724,[]) -> true
    | uu____70728 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____70761 = f  in
      match uu____70761 with
      | (uu____70768,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____70769;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____70770;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____70773;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____70774;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____70775;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____70776;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____70846  ->
                 match uu____70846 with
                 | (y,uu____70855) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____71009 =
                  let uu____71024 =
                    let uu____71027 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____71027  in
                  ((FStar_List.rev pat_binders), uu____71024)  in
                FStar_Pervasives_Native.Some uu____71009
            | (uu____71060,[]) ->
                let uu____71091 =
                  let uu____71106 =
                    let uu____71109 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____71109  in
                  ((FStar_List.rev pat_binders), uu____71106)  in
                FStar_Pervasives_Native.Some uu____71091
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____71200 =
                  let uu____71201 = FStar_Syntax_Subst.compress a  in
                  uu____71201.FStar_Syntax_Syntax.n  in
                (match uu____71200 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____71221 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____71221
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___2188_71251 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___2188_71251.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___2188_71251.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____71255 =
                            let uu____71256 =
                              let uu____71263 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____71263)  in
                            FStar_Syntax_Syntax.NT uu____71256  in
                          [uu____71255]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___2194_71279 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2194_71279.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2194_71279.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____71280 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____71320 =
                  let uu____71335 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____71335  in
                (match uu____71320 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____71410 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____71443 ->
               let uu____71444 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____71444 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____71766 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____71766
       then
         let uu____71771 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____71771
       else ());
      (let uu____71776 = next_prob probs  in
       match uu____71776 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___2219_71803 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___2219_71803.wl_deferred);
               ctr = (uu___2219_71803.ctr);
               defer_ok = (uu___2219_71803.defer_ok);
               smt_ok = (uu___2219_71803.smt_ok);
               umax_heuristic_ok = (uu___2219_71803.umax_heuristic_ok);
               tcenv = (uu___2219_71803.tcenv);
               wl_implicits = (uu___2219_71803.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____71812 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____71812
                 then
                   let uu____71815 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____71815
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
                           (let uu___2231_71827 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___2231_71827.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___2231_71827.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___2231_71827.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___2231_71827.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___2231_71827.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___2231_71827.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___2231_71827.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___2231_71827.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___2231_71827.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____71853 ->
                let uu____71864 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____71935  ->
                          match uu____71935 with
                          | (c,uu____71946,uu____71947) -> c < probs.ctr))
                   in
                (match uu____71864 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____72002 =
                            let uu____72007 =
                              FStar_List.map
                                (fun uu____72025  ->
                                   match uu____72025 with
                                   | (uu____72039,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____72007, (probs.wl_implicits))  in
                          Success uu____72002
                      | uu____72047 ->
                          let uu____72058 =
                            let uu___2249_72059 = probs  in
                            let uu____72060 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____72083  ->
                                      match uu____72083 with
                                      | (uu____72092,uu____72093,y) -> y))
                               in
                            {
                              attempting = uu____72060;
                              wl_deferred = rest;
                              ctr = (uu___2249_72059.ctr);
                              defer_ok = (uu___2249_72059.defer_ok);
                              smt_ok = (uu___2249_72059.smt_ok);
                              umax_heuristic_ok =
                                (uu___2249_72059.umax_heuristic_ok);
                              tcenv = (uu___2249_72059.tcenv);
                              wl_implicits = (uu___2249_72059.wl_implicits)
                            }  in
                          solve env uu____72058))))

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
            let uu____72104 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____72104 with
            | USolved wl1 ->
                let uu____72106 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____72106
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
                  let uu____72160 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____72160 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____72163 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____72176;
                  FStar_Syntax_Syntax.vars = uu____72177;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____72180;
                  FStar_Syntax_Syntax.vars = uu____72181;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____72194,uu____72195) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____72203,FStar_Syntax_Syntax.Tm_uinst uu____72204) ->
                failwith "Impossible: expect head symbols to match"
            | uu____72212 -> USolved wl

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
            ((let uu____72224 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____72224
              then
                let uu____72229 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____72229 msg
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
               let uu____72321 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____72321 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____72376 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____72376
                then
                  let uu____72381 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____72383 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____72381 uu____72383
                else ());
               (let uu____72388 = head_matches_delta env1 wl2 t1 t2  in
                match uu____72388 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____72434 = eq_prob t1 t2 wl2  in
                         (match uu____72434 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____72455 ->
                         let uu____72464 = eq_prob t1 t2 wl2  in
                         (match uu____72464 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____72514 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____72529 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____72530 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____72529, uu____72530)
                           | FStar_Pervasives_Native.None  ->
                               let uu____72535 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____72536 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____72535, uu____72536)
                            in
                         (match uu____72514 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____72567 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____72567 with
                                | (t1_hd,t1_args) ->
                                    let uu____72612 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____72612 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____72678 =
                                              let uu____72685 =
                                                let uu____72696 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____72696 :: t1_args  in
                                              let uu____72713 =
                                                let uu____72722 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____72722 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____72771  ->
                                                   fun uu____72772  ->
                                                     fun uu____72773  ->
                                                       match (uu____72771,
                                                               uu____72772,
                                                               uu____72773)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____72823),
                                                          (a2,uu____72825))
                                                           ->
                                                           let uu____72862 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____72862
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____72685
                                                uu____72713
                                               in
                                            match uu____72678 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___2403_72888 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___2403_72888.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___2403_72888.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___2403_72888.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____72900 =
                                                  solve env1 wl'  in
                                                (match uu____72900 with
                                                 | Success (uu____72903,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___2412_72907
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___2412_72907.attempting);
                                                            wl_deferred =
                                                              (uu___2412_72907.wl_deferred);
                                                            ctr =
                                                              (uu___2412_72907.ctr);
                                                            defer_ok =
                                                              (uu___2412_72907.defer_ok);
                                                            smt_ok =
                                                              (uu___2412_72907.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___2412_72907.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___2412_72907.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____72908 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____72941 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____72941 with
                                | (t1_base,p1_opt) ->
                                    let uu____72977 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____72977 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____73076 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____73076
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
                                               let uu____73129 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____73129
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
                                               let uu____73161 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____73161
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
                                               let uu____73193 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____73193
                                           | uu____73196 -> t_base  in
                                         let uu____73213 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____73213 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____73227 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____73227, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____73234 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____73234 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____73270 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____73270 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____73306 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____73306
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
                              let uu____73330 = combine t11 t21 wl2  in
                              (match uu____73330 with
                               | (t12,ps,wl3) ->
                                   ((let uu____73363 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____73363
                                     then
                                       let uu____73368 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____73368
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____73410 ts1 =
               match uu____73410 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____73473 = pairwise out t wl2  in
                        (match uu____73473 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____73509 =
               let uu____73520 = FStar_List.hd ts  in (uu____73520, [], wl1)
                in
             let uu____73529 = FStar_List.tl ts  in
             aux uu____73509 uu____73529  in
           let uu____73536 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____73536 with
           | (this_flex,this_rigid) ->
               let uu____73562 =
                 let uu____73563 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____73563.FStar_Syntax_Syntax.n  in
               (match uu____73562 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____73588 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____73588
                    then
                      let uu____73591 = destruct_flex_t this_flex wl  in
                      (match uu____73591 with
                       | (flex,wl1) ->
                           let uu____73598 = quasi_pattern env flex  in
                           (match uu____73598 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____73617 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____73617
                                  then
                                    let uu____73622 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____73622
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____73629 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2514_73632 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2514_73632.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2514_73632.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2514_73632.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2514_73632.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2514_73632.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2514_73632.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2514_73632.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2514_73632.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2514_73632.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____73629)
                | uu____73633 ->
                    ((let uu____73635 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____73635
                      then
                        let uu____73640 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____73640
                      else ());
                     (let uu____73645 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____73645 with
                      | (u,_args) ->
                          let uu____73688 =
                            let uu____73689 = FStar_Syntax_Subst.compress u
                               in
                            uu____73689.FStar_Syntax_Syntax.n  in
                          (match uu____73688 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____73717 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____73717 with
                                 | (u',uu____73736) ->
                                     let uu____73761 =
                                       let uu____73762 = whnf env u'  in
                                       uu____73762.FStar_Syntax_Syntax.n  in
                                     (match uu____73761 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____73784 -> false)
                                  in
                               let uu____73786 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___611_73809  ->
                                         match uu___611_73809 with
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
                                              | uu____73823 -> false)
                                         | uu____73827 -> false))
                                  in
                               (match uu____73786 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____73842 = whnf env this_rigid
                                         in
                                      let uu____73843 =
                                        FStar_List.collect
                                          (fun uu___612_73849  ->
                                             match uu___612_73849 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____73855 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____73855]
                                             | uu____73859 -> [])
                                          bounds_probs
                                         in
                                      uu____73842 :: uu____73843  in
                                    let uu____73860 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____73860 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____73893 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____73908 =
                                               let uu____73909 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____73909.FStar_Syntax_Syntax.n
                                                in
                                             match uu____73908 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____73921 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____73921)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____73932 -> bound  in
                                           let uu____73933 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____73933)  in
                                         (match uu____73893 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____73968 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____73968
                                                then
                                                  let wl'1 =
                                                    let uu___2574_73974 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2574_73974.wl_deferred);
                                                      ctr =
                                                        (uu___2574_73974.ctr);
                                                      defer_ok =
                                                        (uu___2574_73974.defer_ok);
                                                      smt_ok =
                                                        (uu___2574_73974.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2574_73974.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2574_73974.tcenv);
                                                      wl_implicits =
                                                        (uu___2574_73974.wl_implicits)
                                                    }  in
                                                  let uu____73975 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____73975
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____73981 =
                                                  solve_t env eq_prob
                                                    (let uu___2579_73983 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2579_73983.wl_deferred);
                                                       ctr =
                                                         (uu___2579_73983.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2579_73983.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2579_73983.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2579_73983.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____73981 with
                                                | Success (uu____73985,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2585_73988 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2585_73988.wl_deferred);
                                                        ctr =
                                                          (uu___2585_73988.ctr);
                                                        defer_ok =
                                                          (uu___2585_73988.defer_ok);
                                                        smt_ok =
                                                          (uu___2585_73988.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2585_73988.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2585_73988.tcenv);
                                                        wl_implicits =
                                                          (uu___2585_73988.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2588_73990 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2588_73990.attempting);
                                                        wl_deferred =
                                                          (uu___2588_73990.wl_deferred);
                                                        ctr =
                                                          (uu___2588_73990.ctr);
                                                        defer_ok =
                                                          (uu___2588_73990.defer_ok);
                                                        smt_ok =
                                                          (uu___2588_73990.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2588_73990.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2588_73990.tcenv);
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
                                                    let uu____74006 =
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
                                                    ((let uu____74020 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____74020
                                                      then
                                                        let uu____74025 =
                                                          let uu____74027 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____74027
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____74025
                                                      else ());
                                                     (let uu____74040 =
                                                        let uu____74055 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____74055)
                                                         in
                                                      match uu____74040 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____74077))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____74103 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____74103
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
                                                                  let uu____74123
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____74123))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____74148 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____74148
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
                                                                    let uu____74168
                                                                    =
                                                                    let uu____74173
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____74173
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____74168
                                                                    [] wl2
                                                                     in
                                                                  let uu____74179
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____74179))))
                                                      | uu____74180 ->
                                                          giveup env
                                                            (Prims.op_Hat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____74196 when flip ->
                               let uu____74197 =
                                 let uu____74199 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____74201 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____74199 uu____74201
                                  in
                               failwith uu____74197
                           | uu____74204 ->
                               let uu____74205 =
                                 let uu____74207 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____74209 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____74207 uu____74209
                                  in
                               failwith uu____74205)))))

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
                      (fun uu____74245  ->
                         match uu____74245 with
                         | (x,i) ->
                             let uu____74264 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____74264, i)) bs_lhs
                     in
                  let uu____74267 = lhs  in
                  match uu____74267 with
                  | (uu____74268,u_lhs,uu____74270) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____74367 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____74377 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____74377, univ)
                             in
                          match uu____74367 with
                          | (k,univ) ->
                              let uu____74384 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____74384 with
                               | (uu____74401,u,wl3) ->
                                   let uu____74404 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____74404, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____74430 =
                              let uu____74443 =
                                let uu____74454 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____74454 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____74505  ->
                                   fun uu____74506  ->
                                     match (uu____74505, uu____74506) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____74607 =
                                           let uu____74614 =
                                             let uu____74617 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____74617
                                              in
                                           copy_uvar u_lhs [] uu____74614 wl2
                                            in
                                         (match uu____74607 with
                                          | (uu____74646,t_a,wl3) ->
                                              let uu____74649 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____74649 with
                                               | (uu____74668,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____74443
                                ([], wl1)
                               in
                            (match uu____74430 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2698_74724 = ct  in
                                   let uu____74725 =
                                     let uu____74728 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____74728
                                      in
                                   let uu____74743 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2698_74724.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2698_74724.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____74725;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____74743;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2698_74724.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2701_74761 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2701_74761.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2701_74761.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____74764 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____74764 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____74826 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____74826 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____74837 =
                                          let uu____74842 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____74842)  in
                                        TERM uu____74837  in
                                      let uu____74843 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____74843 with
                                       | (sub_prob,wl3) ->
                                           let uu____74857 =
                                             let uu____74858 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____74858
                                              in
                                           solve env uu____74857))
                             | (x,imp)::formals2 ->
                                 let uu____74880 =
                                   let uu____74887 =
                                     let uu____74890 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____74890
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____74887 wl1
                                    in
                                 (match uu____74880 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____74911 =
                                          let uu____74914 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____74914
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____74911 u_x
                                         in
                                      let uu____74915 =
                                        let uu____74918 =
                                          let uu____74921 =
                                            let uu____74922 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____74922, imp)  in
                                          [uu____74921]  in
                                        FStar_List.append bs_terms
                                          uu____74918
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____74915 formals2 wl2)
                              in
                           let uu____74949 = occurs_check u_lhs arrow1  in
                           (match uu____74949 with
                            | (uu____74962,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____74978 =
                                    let uu____74980 = FStar_Option.get msg
                                       in
                                    Prims.op_Hat "occurs-check failed: "
                                      uu____74980
                                     in
                                  giveup_or_defer env orig wl uu____74978
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
              (let uu____75013 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____75013
               then
                 let uu____75018 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____75021 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____75018 (rel_to_string (p_rel orig)) uu____75021
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____75148 = rhs wl1 scope env1 subst1  in
                     (match uu____75148 with
                      | (rhs_prob,wl2) ->
                          ((let uu____75169 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____75169
                            then
                              let uu____75174 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____75174
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____75252 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____75252 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2770_75254 = hd1  in
                       let uu____75255 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2770_75254.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2770_75254.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____75255
                       }  in
                     let hd21 =
                       let uu___2773_75259 = hd2  in
                       let uu____75260 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2773_75259.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2773_75259.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____75260
                       }  in
                     let uu____75263 =
                       let uu____75268 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____75268
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____75263 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____75289 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____75289
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____75296 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____75296 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____75363 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____75363
                                  in
                               ((let uu____75381 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____75381
                                 then
                                   let uu____75386 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____75388 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____75386
                                     uu____75388
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____75421 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____75457 = aux wl [] env [] bs1 bs2  in
               match uu____75457 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____75512 = attempt sub_probs wl2  in
                   solve env uu____75512)

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
            let uu___2808_75533 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2808_75533.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2808_75533.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____75546 = try_solve env wl'  in
          match uu____75546 with
          | Success (uu____75547,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2817_75551 = wl  in
                  {
                    attempting = (uu___2817_75551.attempting);
                    wl_deferred = (uu___2817_75551.wl_deferred);
                    ctr = (uu___2817_75551.ctr);
                    defer_ok = (uu___2817_75551.defer_ok);
                    smt_ok = (uu___2817_75551.smt_ok);
                    umax_heuristic_ok = (uu___2817_75551.umax_heuristic_ok);
                    tcenv = (uu___2817_75551.tcenv);
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
        (let uu____75563 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____75563 wl)

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
              let uu____75577 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____75577 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____75611 = lhs1  in
              match uu____75611 with
              | (uu____75614,ctx_u,uu____75616) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____75624 ->
                        let uu____75625 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____75625 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____75674 = quasi_pattern env1 lhs1  in
              match uu____75674 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____75708) ->
                  let uu____75713 = lhs1  in
                  (match uu____75713 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____75728 = occurs_check ctx_u rhs1  in
                       (match uu____75728 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____75779 =
                                let uu____75787 =
                                  let uu____75789 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____75789
                                   in
                                FStar_Util.Inl uu____75787  in
                              (uu____75779, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____75817 =
                                 let uu____75819 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____75819  in
                               if uu____75817
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____75846 =
                                    let uu____75854 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____75854  in
                                  let uu____75860 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____75846, uu____75860)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____75904 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____75904 with
              | (rhs_hd,args) ->
                  let uu____75947 = FStar_Util.prefix args  in
                  (match uu____75947 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____76019 = lhs1  in
                       (match uu____76019 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____76023 =
                              let uu____76034 =
                                let uu____76041 =
                                  let uu____76044 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____76044
                                   in
                                copy_uvar u_lhs [] uu____76041 wl1  in
                              match uu____76034 with
                              | (uu____76071,t_last_arg,wl2) ->
                                  let uu____76074 =
                                    let uu____76081 =
                                      let uu____76082 =
                                        let uu____76091 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____76091]  in
                                      FStar_List.append bs_lhs uu____76082
                                       in
                                    copy_uvar u_lhs uu____76081 t_res_lhs wl2
                                     in
                                  (match uu____76074 with
                                   | (uu____76126,lhs',wl3) ->
                                       let uu____76129 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____76129 with
                                        | (uu____76146,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____76023 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____76167 =
                                     let uu____76168 =
                                       let uu____76173 =
                                         let uu____76174 =
                                           let uu____76177 =
                                             let uu____76182 =
                                               let uu____76183 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____76183]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____76182
                                              in
                                           uu____76177
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____76174
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____76173)  in
                                     TERM uu____76168  in
                                   [uu____76167]  in
                                 let uu____76208 =
                                   let uu____76215 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____76215 with
                                   | (p1,wl3) ->
                                       let uu____76235 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____76235 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____76208 with
                                  | (sub_probs,wl3) ->
                                      let uu____76267 =
                                        let uu____76268 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____76268  in
                                      solve env1 uu____76267))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____76302 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____76302 with
                | (uu____76320,args) ->
                    (match args with | [] -> false | uu____76356 -> true)
                 in
              let is_arrow rhs2 =
                let uu____76375 =
                  let uu____76376 = FStar_Syntax_Subst.compress rhs2  in
                  uu____76376.FStar_Syntax_Syntax.n  in
                match uu____76375 with
                | FStar_Syntax_Syntax.Tm_arrow uu____76380 -> true
                | uu____76396 -> false  in
              let uu____76398 = quasi_pattern env1 lhs1  in
              match uu____76398 with
              | FStar_Pervasives_Native.None  ->
                  let uu____76409 =
                    let uu____76411 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                      uu____76411
                     in
                  giveup_or_defer env1 orig1 wl1 uu____76409
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____76420 = is_app rhs1  in
                  if uu____76420
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____76425 = is_arrow rhs1  in
                     if uu____76425
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____76430 =
                          let uu____76432 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heuristic cannot solve %s; rhs not an app or arrow"
                            uu____76432
                           in
                        giveup_or_defer env1 orig1 wl1 uu____76430))
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
                let uu____76443 = lhs  in
                (match uu____76443 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____76447 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____76447 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____76465 =
                              let uu____76469 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____76469
                               in
                            FStar_All.pipe_right uu____76465
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____76490 = occurs_check ctx_uv rhs1  in
                          (match uu____76490 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____76519 =
                                   let uu____76521 = FStar_Option.get msg  in
                                   Prims.op_Hat "occurs-check failed: "
                                     uu____76521
                                    in
                                 giveup_or_defer env orig wl uu____76519
                               else
                                 (let uu____76527 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____76527
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____76534 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____76534
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____76538 =
                                         let uu____76540 =
                                           names_to_string1 fvs2  in
                                         let uu____76542 =
                                           names_to_string1 fvs1  in
                                         let uu____76544 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____76540 uu____76542
                                           uu____76544
                                          in
                                       giveup_or_defer env orig wl
                                         uu____76538)
                                    else first_order orig env wl lhs rhs1))
                      | uu____76556 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____76563 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____76563 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____76589 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____76589
                             | (FStar_Util.Inl msg,uu____76591) ->
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
                  (let uu____76636 =
                     let uu____76653 = quasi_pattern env lhs  in
                     let uu____76660 = quasi_pattern env rhs  in
                     (uu____76653, uu____76660)  in
                   match uu____76636 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____76703 = lhs  in
                       (match uu____76703 with
                        | ({ FStar_Syntax_Syntax.n = uu____76704;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____76706;_},u_lhs,uu____76708)
                            ->
                            let uu____76711 = rhs  in
                            (match uu____76711 with
                             | (uu____76712,u_rhs,uu____76714) ->
                                 let uu____76715 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____76715
                                 then
                                   let uu____76722 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____76722
                                 else
                                   (let uu____76725 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____76725 with
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
                                        let uu____76757 =
                                          let uu____76764 =
                                            let uu____76767 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____76767
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____76764
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____76757 with
                                         | (uu____76779,w,wl1) ->
                                             let w_app =
                                               let uu____76785 =
                                                 let uu____76790 =
                                                   FStar_List.map
                                                     (fun uu____76801  ->
                                                        match uu____76801
                                                        with
                                                        | (z,uu____76809) ->
                                                            let uu____76814 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____76814) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____76790
                                                  in
                                               uu____76785
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____76816 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____76816
                                               then
                                                 let uu____76821 =
                                                   let uu____76825 =
                                                     flex_t_to_string lhs  in
                                                   let uu____76827 =
                                                     let uu____76831 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____76833 =
                                                       let uu____76837 =
                                                         term_to_string w  in
                                                       let uu____76839 =
                                                         let uu____76843 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____76852 =
                                                           let uu____76856 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____76865 =
                                                             let uu____76869
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____76869]
                                                              in
                                                           uu____76856 ::
                                                             uu____76865
                                                            in
                                                         uu____76843 ::
                                                           uu____76852
                                                          in
                                                       uu____76837 ::
                                                         uu____76839
                                                        in
                                                     uu____76831 ::
                                                       uu____76833
                                                      in
                                                   uu____76825 :: uu____76827
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____76821
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____76886 =
                                                     let uu____76891 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____76891)  in
                                                   TERM uu____76886  in
                                                 let uu____76892 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____76892
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____76900 =
                                                        let uu____76905 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____76905)
                                                         in
                                                      TERM uu____76900  in
                                                    [s1; s2])
                                                  in
                                               let uu____76906 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____76906))))))
                   | uu____76907 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____76978 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____76978
            then
              let uu____76983 = FStar_Syntax_Print.term_to_string t1  in
              let uu____76985 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____76987 = FStar_Syntax_Print.term_to_string t2  in
              let uu____76989 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____76983 uu____76985 uu____76987 uu____76989
            else ());
           (let uu____77000 = FStar_Syntax_Util.head_and_args t1  in
            match uu____77000 with
            | (head1,args1) ->
                let uu____77043 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____77043 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____77113 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____77113 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              k false (defer "universe constraints" orig wl3))
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____77139 =
                         let uu____77141 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____77143 = args_to_string args1  in
                         let uu____77147 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____77149 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____77141 uu____77143 uu____77147 uu____77149
                          in
                       giveup env1 uu____77139 orig
                     else
                       (let uu____77156 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____77161 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____77161 = FStar_Syntax_Util.Equal)
                           in
                        if uu____77156
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___3066_77165 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___3066_77165.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___3066_77165.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___3066_77165.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___3066_77165.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___3066_77165.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___3066_77165.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___3066_77165.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___3066_77165.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____77175 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____77175
                                    else solve env1 wl2))
                        else
                          (let uu____77180 = base_and_refinement env1 t1  in
                           match uu____77180 with
                           | (base1,refinement1) ->
                               let uu____77205 = base_and_refinement env1 t2
                                  in
                               (match uu____77205 with
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
                                           let uu____77370 =
                                             FStar_List.fold_right
                                               (fun uu____77410  ->
                                                  fun uu____77411  ->
                                                    match (uu____77410,
                                                            uu____77411)
                                                    with
                                                    | (((a1,uu____77463),
                                                        (a2,uu____77465)),
                                                       (probs,wl3)) ->
                                                        let uu____77514 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____77514
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____77370 with
                                           | (subprobs,wl3) ->
                                               ((let uu____77557 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____77557
                                                 then
                                                   let uu____77562 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____77562
                                                 else ());
                                                (let uu____77568 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____77568
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
                                                    (let uu____77595 =
                                                       mk_sub_probs wl3  in
                                                     match uu____77595 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____77611 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____77611
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____77619 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____77619))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____77643 =
                                                    mk_sub_probs wl3  in
                                                  match uu____77643 with
                                                  | (subprobs,wl4) ->
                                                      let wl5 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          [] wl4
                                                         in
                                                      let uu____77657 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____77657)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____77683 =
                                           match uu____77683 with
                                           | (prob,reason) ->
                                               ((let uu____77694 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____77694
                                                 then
                                                   let uu____77699 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____77701 =
                                                     prob_to_string env2 prob
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____77699 uu____77701
                                                     reason
                                                 else ());
                                                (let uu____77706 =
                                                   let uu____77715 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____77718 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____77715, uu____77718)
                                                    in
                                                 match uu____77706 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____77731 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____77731 with
                                                      | (head1',uu____77749)
                                                          ->
                                                          let uu____77774 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____77774
                                                           with
                                                           | (head2',uu____77792)
                                                               ->
                                                               let uu____77817
                                                                 =
                                                                 let uu____77822
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____77823
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____77822,
                                                                   uu____77823)
                                                                  in
                                                               (match uu____77817
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____77825
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____77825
                                                                    then
                                                                    let uu____77830
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____77832
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____77834
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____77836
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____77830
                                                                    uu____77832
                                                                    uu____77834
                                                                    uu____77836
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____77841
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___3152_77849
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___3152_77849.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___3152_77849.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___3152_77849.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___3152_77849.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___3152_77849.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___3152_77849.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___3152_77849.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___3152_77849.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____77851
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____77851
                                                                    then
                                                                    let uu____77856
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____77856
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____77861 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____77873 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____77873 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____77881 =
                                             let uu____77882 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____77882.FStar_Syntax_Syntax.n
                                              in
                                           match uu____77881 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____77887 -> false  in
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
                                          | uu____77890 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____77893 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___3172_77929 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___3172_77929.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___3172_77929.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___3172_77929.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___3172_77929.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___3172_77929.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___3172_77929.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___3172_77929.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___3172_77929.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____78005 = destruct_flex_t scrutinee wl1  in
             match uu____78005 with
             | ((_t,uv,_args),wl2) ->
                 let uu____78016 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____78016 with
                  | (xs,pat_term,uu____78032,uu____78033) ->
                      let uu____78038 =
                        FStar_List.fold_left
                          (fun uu____78061  ->
                             fun x  ->
                               match uu____78061 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____78082 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____78082 with
                                    | (uu____78101,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____78038 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____78122 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____78122 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___3212_78139 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___3212_78139.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___3212_78139.umax_heuristic_ok);
                                    tcenv = (uu___3212_78139.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____78151 = solve env1 wl'  in
                                (match uu____78151 with
                                 | Success (uu____78154,imps) ->
                                     let wl'1 =
                                       let uu___3220_78157 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___3220_78157.wl_deferred);
                                         ctr = (uu___3220_78157.ctr);
                                         defer_ok =
                                           (uu___3220_78157.defer_ok);
                                         smt_ok = (uu___3220_78157.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___3220_78157.umax_heuristic_ok);
                                         tcenv = (uu___3220_78157.tcenv);
                                         wl_implicits =
                                           (uu___3220_78157.wl_implicits)
                                       }  in
                                     let uu____78158 = solve env1 wl'1  in
                                     (match uu____78158 with
                                      | Success (uu____78161,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___3228_78165 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___3228_78165.attempting);
                                                 wl_deferred =
                                                   (uu___3228_78165.wl_deferred);
                                                 ctr = (uu___3228_78165.ctr);
                                                 defer_ok =
                                                   (uu___3228_78165.defer_ok);
                                                 smt_ok =
                                                   (uu___3228_78165.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3228_78165.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3228_78165.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____78166 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____78173 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____78196 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____78196
                 then
                   let uu____78201 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____78203 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____78201 uu____78203
                 else ());
                (let uu____78208 =
                   let uu____78229 =
                     let uu____78238 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____78238)  in
                   let uu____78245 =
                     let uu____78254 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____78254)  in
                   (uu____78229, uu____78245)  in
                 match uu____78208 with
                 | ((uu____78284,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____78287;
                                   FStar_Syntax_Syntax.vars = uu____78288;_}),
                    (s,t)) ->
                     let uu____78359 =
                       let uu____78361 = is_flex scrutinee  in
                       Prims.op_Negation uu____78361  in
                     if uu____78359
                     then
                       ((let uu____78372 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____78372
                         then
                           let uu____78377 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____78377
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____78396 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____78396
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____78411 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____78411
                           then
                             let uu____78416 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____78418 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____78416 uu____78418
                           else ());
                          (let pat_discriminates uu___613_78443 =
                             match uu___613_78443 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____78459;
                                  FStar_Syntax_Syntax.p = uu____78460;_},FStar_Pervasives_Native.None
                                ,uu____78461) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____78475;
                                  FStar_Syntax_Syntax.p = uu____78476;_},FStar_Pervasives_Native.None
                                ,uu____78477) -> true
                             | uu____78504 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____78607 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____78607 with
                                       | (uu____78609,uu____78610,t') ->
                                           let uu____78628 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____78628 with
                                            | (FullMatch ,uu____78640) ->
                                                true
                                            | (HeadMatch
                                               uu____78654,uu____78655) ->
                                                true
                                            | uu____78670 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____78707 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____78707
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____78718 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____78718 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____78806,uu____78807) ->
                                       branches1
                                   | uu____78952 -> branches  in
                                 let uu____79007 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____79016 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____79016 with
                                        | (p,uu____79020,uu____79021) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _79050  -> FStar_Util.Inr _79050)
                                   uu____79007))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____79080 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____79080 with
                                | (p,uu____79089,e) ->
                                    ((let uu____79108 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____79108
                                      then
                                        let uu____79113 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____79115 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____79113 uu____79115
                                      else ());
                                     (let uu____79120 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _79135  -> FStar_Util.Inr _79135)
                                        uu____79120)))))
                 | ((s,t),(uu____79138,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____79141;
                                         FStar_Syntax_Syntax.vars =
                                           uu____79142;_}))
                     ->
                     let uu____79211 =
                       let uu____79213 = is_flex scrutinee  in
                       Prims.op_Negation uu____79213  in
                     if uu____79211
                     then
                       ((let uu____79224 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____79224
                         then
                           let uu____79229 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____79229
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____79248 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____79248
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____79263 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____79263
                           then
                             let uu____79268 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____79270 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____79268 uu____79270
                           else ());
                          (let pat_discriminates uu___613_79295 =
                             match uu___613_79295 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____79311;
                                  FStar_Syntax_Syntax.p = uu____79312;_},FStar_Pervasives_Native.None
                                ,uu____79313) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____79327;
                                  FStar_Syntax_Syntax.p = uu____79328;_},FStar_Pervasives_Native.None
                                ,uu____79329) -> true
                             | uu____79356 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____79459 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____79459 with
                                       | (uu____79461,uu____79462,t') ->
                                           let uu____79480 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____79480 with
                                            | (FullMatch ,uu____79492) ->
                                                true
                                            | (HeadMatch
                                               uu____79506,uu____79507) ->
                                                true
                                            | uu____79522 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____79559 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____79559
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____79570 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____79570 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____79658,uu____79659) ->
                                       branches1
                                   | uu____79804 -> branches  in
                                 let uu____79859 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____79868 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____79868 with
                                        | (p,uu____79872,uu____79873) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _79902  -> FStar_Util.Inr _79902)
                                   uu____79859))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____79932 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____79932 with
                                | (p,uu____79941,e) ->
                                    ((let uu____79960 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____79960
                                      then
                                        let uu____79965 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____79967 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____79965 uu____79967
                                      else ());
                                     (let uu____79972 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _79987  -> FStar_Util.Inr _79987)
                                        uu____79972)))))
                 | uu____79988 ->
                     ((let uu____80010 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____80010
                       then
                         let uu____80015 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____80017 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____80015 uu____80017
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____80063 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____80063
            then
              let uu____80068 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____80070 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____80072 = FStar_Syntax_Print.term_to_string t1  in
              let uu____80074 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____80068 uu____80070 uu____80072 uu____80074
            else ());
           (let uu____80079 = head_matches_delta env1 wl1 t1 t2  in
            match uu____80079 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____80110,uu____80111) ->
                     let rec may_relate head3 =
                       let uu____80139 =
                         let uu____80140 = FStar_Syntax_Subst.compress head3
                            in
                         uu____80140.FStar_Syntax_Syntax.n  in
                       match uu____80139 with
                       | FStar_Syntax_Syntax.Tm_name uu____80144 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____80146 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____80171 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____80171 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____80173 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____80176
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____80177 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____80180,uu____80181) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____80223) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____80229) ->
                           may_relate t
                       | uu____80234 -> false  in
                     let uu____80236 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____80236 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____80257 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____80257
                          then
                            let uu____80260 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____80260 with
                             | (guard,wl2) ->
                                 let uu____80267 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____80267)
                          else
                            (let uu____80270 =
                               let uu____80272 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____80274 =
                                 let uu____80276 =
                                   let uu____80280 =
                                     delta_depth_of_term env1 head1  in
                                   FStar_Util.bind_opt uu____80280
                                     (fun x  ->
                                        let uu____80287 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____80287)
                                    in
                                 FStar_Util.dflt "" uu____80276  in
                               let uu____80292 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               let uu____80294 =
                                 let uu____80296 =
                                   let uu____80300 =
                                     delta_depth_of_term env1 head2  in
                                   FStar_Util.bind_opt uu____80300
                                     (fun x  ->
                                        let uu____80307 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____80307)
                                    in
                                 FStar_Util.dflt "" uu____80296  in
                               FStar_Util.format4
                                 "head mismatch (%s (%s) vs %s (%s))"
                                 uu____80272 uu____80274 uu____80292
                                 uu____80294
                                in
                             giveup env1 uu____80270 orig))
                 | (HeadMatch (true ),uu____80313) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____80328 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____80328 with
                        | (guard,wl2) ->
                            let uu____80335 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____80335)
                     else
                       (let uu____80338 =
                          let uu____80340 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____80342 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____80340 uu____80342
                           in
                        giveup env1 uu____80338 orig)
                 | (uu____80345,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___3401_80359 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___3401_80359.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___3401_80359.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___3401_80359.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___3401_80359.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___3401_80359.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___3401_80359.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___3401_80359.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___3401_80359.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____80386 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____80386
          then
            let uu____80389 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____80389
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____80395 =
                let uu____80398 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____80398  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____80395 t1);
             (let uu____80417 =
                let uu____80420 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____80420  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____80417 t2);
             (let uu____80439 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____80439
              then
                let uu____80443 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____80445 =
                  let uu____80447 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____80449 =
                    let uu____80451 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____80451  in
                  Prims.op_Hat uu____80447 uu____80449  in
                let uu____80454 =
                  let uu____80456 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____80458 =
                    let uu____80460 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____80460  in
                  Prims.op_Hat uu____80456 uu____80458  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____80443 uu____80445 uu____80454
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____80467,uu____80468) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____80492,FStar_Syntax_Syntax.Tm_delayed uu____80493) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____80517,uu____80518) ->
                  let uu____80545 =
                    let uu___3432_80546 = problem  in
                    let uu____80547 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3432_80546.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____80547;
                      FStar_TypeChecker_Common.relation =
                        (uu___3432_80546.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3432_80546.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3432_80546.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3432_80546.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3432_80546.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3432_80546.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3432_80546.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3432_80546.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____80545 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____80548,uu____80549) ->
                  let uu____80556 =
                    let uu___3438_80557 = problem  in
                    let uu____80558 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3438_80557.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____80558;
                      FStar_TypeChecker_Common.relation =
                        (uu___3438_80557.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3438_80557.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3438_80557.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3438_80557.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3438_80557.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3438_80557.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3438_80557.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3438_80557.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____80556 wl
              | (uu____80559,FStar_Syntax_Syntax.Tm_ascribed uu____80560) ->
                  let uu____80587 =
                    let uu___3444_80588 = problem  in
                    let uu____80589 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3444_80588.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3444_80588.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3444_80588.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____80589;
                      FStar_TypeChecker_Common.element =
                        (uu___3444_80588.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3444_80588.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3444_80588.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3444_80588.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3444_80588.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3444_80588.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____80587 wl
              | (uu____80590,FStar_Syntax_Syntax.Tm_meta uu____80591) ->
                  let uu____80598 =
                    let uu___3450_80599 = problem  in
                    let uu____80600 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3450_80599.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3450_80599.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3450_80599.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____80600;
                      FStar_TypeChecker_Common.element =
                        (uu___3450_80599.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3450_80599.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3450_80599.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3450_80599.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3450_80599.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3450_80599.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____80598 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____80602),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____80604)) ->
                  let uu____80613 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____80613
              | (FStar_Syntax_Syntax.Tm_bvar uu____80614,uu____80615) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____80617,FStar_Syntax_Syntax.Tm_bvar uu____80618) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___614_80688 =
                    match uu___614_80688 with
                    | [] -> c
                    | bs ->
                        let uu____80716 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____80716
                     in
                  let uu____80727 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____80727 with
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
                                    let uu____80876 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____80876
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
                  let mk_t t l uu___615_80965 =
                    match uu___615_80965 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____81007 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____81007 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____81152 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____81153 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____81152
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____81153 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____81155,uu____81156) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____81187 -> true
                    | uu____81207 -> false  in
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
                      (let uu____81267 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3552_81275 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3552_81275.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3552_81275.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3552_81275.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3552_81275.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3552_81275.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3552_81275.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3552_81275.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3552_81275.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3552_81275.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___3552_81275.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3552_81275.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3552_81275.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3552_81275.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3552_81275.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3552_81275.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3552_81275.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3552_81275.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3552_81275.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3552_81275.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3552_81275.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3552_81275.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3552_81275.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3552_81275.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3552_81275.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3552_81275.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3552_81275.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3552_81275.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3552_81275.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3552_81275.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3552_81275.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3552_81275.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3552_81275.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3552_81275.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3552_81275.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3552_81275.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3552_81275.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3552_81275.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3552_81275.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3552_81275.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3552_81275.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____81267 with
                       | (uu____81280,ty,uu____81282) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____81291 =
                                 let uu____81292 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____81292.FStar_Syntax_Syntax.n  in
                               match uu____81291 with
                               | FStar_Syntax_Syntax.Tm_refine uu____81295 ->
                                   let uu____81302 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____81302
                               | uu____81303 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____81306 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____81306
                             then
                               let uu____81311 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____81313 =
                                 let uu____81315 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____81315
                                  in
                               let uu____81316 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____81311 uu____81313 uu____81316
                             else ());
                            r1))
                     in
                  let uu____81321 =
                    let uu____81338 = maybe_eta t1  in
                    let uu____81345 = maybe_eta t2  in
                    (uu____81338, uu____81345)  in
                  (match uu____81321 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3573_81387 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3573_81387.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3573_81387.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3573_81387.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3573_81387.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3573_81387.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3573_81387.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3573_81387.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3573_81387.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____81408 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____81408
                       then
                         let uu____81411 = destruct_flex_t not_abs wl  in
                         (match uu____81411 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_81428 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_81428.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_81428.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_81428.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_81428.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_81428.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_81428.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_81428.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_81428.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____81452 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____81452
                       then
                         let uu____81455 = destruct_flex_t not_abs wl  in
                         (match uu____81455 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_81472 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_81472.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_81472.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_81472.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_81472.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_81472.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_81472.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_81472.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_81472.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____81476 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____81494,FStar_Syntax_Syntax.Tm_abs uu____81495) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____81526 -> true
                    | uu____81546 -> false  in
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
                      (let uu____81606 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3552_81614 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3552_81614.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3552_81614.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3552_81614.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3552_81614.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3552_81614.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3552_81614.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3552_81614.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3552_81614.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3552_81614.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___3552_81614.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3552_81614.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3552_81614.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3552_81614.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3552_81614.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3552_81614.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3552_81614.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3552_81614.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3552_81614.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3552_81614.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3552_81614.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3552_81614.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3552_81614.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3552_81614.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3552_81614.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3552_81614.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3552_81614.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3552_81614.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3552_81614.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3552_81614.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3552_81614.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3552_81614.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3552_81614.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3552_81614.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3552_81614.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3552_81614.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3552_81614.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3552_81614.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3552_81614.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3552_81614.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3552_81614.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____81606 with
                       | (uu____81619,ty,uu____81621) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____81630 =
                                 let uu____81631 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____81631.FStar_Syntax_Syntax.n  in
                               match uu____81630 with
                               | FStar_Syntax_Syntax.Tm_refine uu____81634 ->
                                   let uu____81641 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____81641
                               | uu____81642 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____81645 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____81645
                             then
                               let uu____81650 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____81652 =
                                 let uu____81654 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____81654
                                  in
                               let uu____81655 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____81650 uu____81652 uu____81655
                             else ());
                            r1))
                     in
                  let uu____81660 =
                    let uu____81677 = maybe_eta t1  in
                    let uu____81684 = maybe_eta t2  in
                    (uu____81677, uu____81684)  in
                  (match uu____81660 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3573_81726 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3573_81726.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3573_81726.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3573_81726.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3573_81726.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3573_81726.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3573_81726.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3573_81726.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3573_81726.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____81747 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____81747
                       then
                         let uu____81750 = destruct_flex_t not_abs wl  in
                         (match uu____81750 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_81767 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_81767.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_81767.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_81767.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_81767.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_81767.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_81767.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_81767.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_81767.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____81791 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____81791
                       then
                         let uu____81794 = destruct_flex_t not_abs wl  in
                         (match uu____81794 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_81811 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_81811.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_81811.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_81811.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_81811.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_81811.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_81811.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_81811.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_81811.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____81815 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____81845 =
                    let uu____81850 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____81850 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3613_81878 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3613_81878.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3613_81878.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3615_81880 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3615_81880.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3615_81880.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____81881,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3613_81896 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3613_81896.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3613_81896.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3615_81898 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3615_81898.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3615_81898.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____81899 -> (x1, x2)  in
                  (match uu____81845 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____81918 = as_refinement false env t11  in
                       (match uu____81918 with
                        | (x12,phi11) ->
                            let uu____81926 = as_refinement false env t21  in
                            (match uu____81926 with
                             | (x22,phi21) ->
                                 ((let uu____81935 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____81935
                                   then
                                     ((let uu____81940 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____81942 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____81944 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____81940
                                         uu____81942 uu____81944);
                                      (let uu____81947 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____81949 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____81951 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____81947
                                         uu____81949 uu____81951))
                                   else ());
                                  (let uu____81956 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____81956 with
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
                                         let uu____82027 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____82027
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____82039 =
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
                                         (let uu____82052 =
                                            let uu____82055 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____82055
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____82052
                                            (p_guard base_prob));
                                         (let uu____82074 =
                                            let uu____82077 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____82077
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____82074
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____82096 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____82096)
                                          in
                                       let has_uvars =
                                         (let uu____82101 =
                                            let uu____82103 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____82103
                                             in
                                          Prims.op_Negation uu____82101) ||
                                           (let uu____82107 =
                                              let uu____82109 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____82109
                                               in
                                            Prims.op_Negation uu____82107)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____82113 =
                                           let uu____82118 =
                                             let uu____82127 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____82127]  in
                                           mk_t_problem wl1 uu____82118 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____82113 with
                                          | (ref_prob,wl2) ->
                                              let uu____82149 =
                                                solve env1
                                                  (let uu___3657_82151 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3657_82151.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3657_82151.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3657_82151.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3657_82151.tcenv);
                                                     wl_implicits =
                                                       (uu___3657_82151.wl_implicits)
                                                   })
                                                 in
                                              (match uu____82149 with
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
                                               | Success uu____82168 ->
                                                   let guard =
                                                     let uu____82176 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____82176
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___3668_82185 =
                                                       wl3  in
                                                     {
                                                       attempting =
                                                         (uu___3668_82185.attempting);
                                                       wl_deferred =
                                                         (uu___3668_82185.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            (Prims.parse_int "1"));
                                                       defer_ok =
                                                         (uu___3668_82185.defer_ok);
                                                       smt_ok =
                                                         (uu___3668_82185.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___3668_82185.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___3668_82185.tcenv);
                                                       wl_implicits =
                                                         (uu___3668_82185.wl_implicits)
                                                     }  in
                                                   let uu____82187 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____82187))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____82190,FStar_Syntax_Syntax.Tm_uvar uu____82191) ->
                  let uu____82216 = destruct_flex_t t1 wl  in
                  (match uu____82216 with
                   | (f1,wl1) ->
                       let uu____82223 = destruct_flex_t t2 wl1  in
                       (match uu____82223 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82230;
                    FStar_Syntax_Syntax.pos = uu____82231;
                    FStar_Syntax_Syntax.vars = uu____82232;_},uu____82233),FStar_Syntax_Syntax.Tm_uvar
                 uu____82234) ->
                  let uu____82283 = destruct_flex_t t1 wl  in
                  (match uu____82283 with
                   | (f1,wl1) ->
                       let uu____82290 = destruct_flex_t t2 wl1  in
                       (match uu____82290 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____82297,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82298;
                    FStar_Syntax_Syntax.pos = uu____82299;
                    FStar_Syntax_Syntax.vars = uu____82300;_},uu____82301))
                  ->
                  let uu____82350 = destruct_flex_t t1 wl  in
                  (match uu____82350 with
                   | (f1,wl1) ->
                       let uu____82357 = destruct_flex_t t2 wl1  in
                       (match uu____82357 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82364;
                    FStar_Syntax_Syntax.pos = uu____82365;
                    FStar_Syntax_Syntax.vars = uu____82366;_},uu____82367),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82368;
                    FStar_Syntax_Syntax.pos = uu____82369;
                    FStar_Syntax_Syntax.vars = uu____82370;_},uu____82371))
                  ->
                  let uu____82444 = destruct_flex_t t1 wl  in
                  (match uu____82444 with
                   | (f1,wl1) ->
                       let uu____82451 = destruct_flex_t t2 wl1  in
                       (match uu____82451 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____82458,uu____82459) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____82472 = destruct_flex_t t1 wl  in
                  (match uu____82472 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82479;
                    FStar_Syntax_Syntax.pos = uu____82480;
                    FStar_Syntax_Syntax.vars = uu____82481;_},uu____82482),uu____82483)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____82520 = destruct_flex_t t1 wl  in
                  (match uu____82520 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____82527,FStar_Syntax_Syntax.Tm_uvar uu____82528) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____82541,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82542;
                    FStar_Syntax_Syntax.pos = uu____82543;
                    FStar_Syntax_Syntax.vars = uu____82544;_},uu____82545))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____82582,FStar_Syntax_Syntax.Tm_arrow uu____82583) ->
                  solve_t' env
                    (let uu___3768_82611 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3768_82611.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3768_82611.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3768_82611.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3768_82611.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3768_82611.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3768_82611.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3768_82611.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3768_82611.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3768_82611.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82612;
                    FStar_Syntax_Syntax.pos = uu____82613;
                    FStar_Syntax_Syntax.vars = uu____82614;_},uu____82615),FStar_Syntax_Syntax.Tm_arrow
                 uu____82616) ->
                  solve_t' env
                    (let uu___3768_82668 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3768_82668.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3768_82668.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3768_82668.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3768_82668.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3768_82668.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3768_82668.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3768_82668.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3768_82668.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3768_82668.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____82669,FStar_Syntax_Syntax.Tm_uvar uu____82670) ->
                  let uu____82683 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____82683
              | (uu____82684,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82685;
                    FStar_Syntax_Syntax.pos = uu____82686;
                    FStar_Syntax_Syntax.vars = uu____82687;_},uu____82688))
                  ->
                  let uu____82725 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____82725
              | (FStar_Syntax_Syntax.Tm_uvar uu____82726,uu____82727) ->
                  let uu____82740 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____82740
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82741;
                    FStar_Syntax_Syntax.pos = uu____82742;
                    FStar_Syntax_Syntax.vars = uu____82743;_},uu____82744),uu____82745)
                  ->
                  let uu____82782 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____82782
              | (FStar_Syntax_Syntax.Tm_refine uu____82783,uu____82784) ->
                  let t21 =
                    let uu____82792 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____82792  in
                  solve_t env
                    (let uu___3803_82818 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3803_82818.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3803_82818.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3803_82818.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3803_82818.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3803_82818.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3803_82818.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3803_82818.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3803_82818.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3803_82818.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____82819,FStar_Syntax_Syntax.Tm_refine uu____82820) ->
                  let t11 =
                    let uu____82828 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____82828  in
                  solve_t env
                    (let uu___3810_82854 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3810_82854.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3810_82854.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3810_82854.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3810_82854.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3810_82854.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3810_82854.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3810_82854.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3810_82854.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3810_82854.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____82936 =
                    let uu____82937 = guard_of_prob env wl problem t1 t2  in
                    match uu____82937 with
                    | (guard,wl1) ->
                        let uu____82944 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____82944
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____83163 = br1  in
                        (match uu____83163 with
                         | (p1,w1,uu____83192) ->
                             let uu____83209 = br2  in
                             (match uu____83209 with
                              | (p2,w2,uu____83232) ->
                                  let uu____83237 =
                                    let uu____83239 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____83239  in
                                  if uu____83237
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____83266 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____83266 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____83303 = br2  in
                                         (match uu____83303 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____83336 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____83336
                                                 in
                                              let uu____83341 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____83372,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____83393) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____83452 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____83452 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____83341
                                                (fun uu____83524  ->
                                                   match uu____83524 with
                                                   | (wprobs,wl2) ->
                                                       let uu____83561 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____83561
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____83582
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____83582
                                                              then
                                                                let uu____83587
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____83589
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____83587
                                                                  uu____83589
                                                              else ());
                                                             (let uu____83595
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____83595
                                                                (fun
                                                                   uu____83631
                                                                    ->
                                                                   match uu____83631
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
                    | uu____83760 -> FStar_Pervasives_Native.None  in
                  let uu____83801 = solve_branches wl brs1 brs2  in
                  (match uu____83801 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____83852 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____83852 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____83886 =
                                FStar_List.map
                                  (fun uu____83898  ->
                                     match uu____83898 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____83886  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____83907 =
                              let uu____83908 =
                                let uu____83909 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____83909
                                  (let uu___3909_83917 = wl3  in
                                   {
                                     attempting =
                                       (uu___3909_83917.attempting);
                                     wl_deferred =
                                       (uu___3909_83917.wl_deferred);
                                     ctr = (uu___3909_83917.ctr);
                                     defer_ok = (uu___3909_83917.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3909_83917.umax_heuristic_ok);
                                     tcenv = (uu___3909_83917.tcenv);
                                     wl_implicits =
                                       (uu___3909_83917.wl_implicits)
                                   })
                                 in
                              solve env uu____83908  in
                            (match uu____83907 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____83922 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____83929,uu____83930) ->
                  let head1 =
                    let uu____83954 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____83954
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84000 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84000
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____84046 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____84046
                    then
                      let uu____84050 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____84052 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____84054 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____84050 uu____84052 uu____84054
                    else ());
                   (let no_free_uvars t =
                      (let uu____84068 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____84068) &&
                        (let uu____84072 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____84072)
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
                      let uu____84089 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____84089 = FStar_Syntax_Util.Equal  in
                    let uu____84090 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____84090
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____84094 = equal t1 t2  in
                         (if uu____84094
                          then
                            let uu____84097 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____84097
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____84102 =
                            let uu____84109 = equal t1 t2  in
                            if uu____84109
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____84122 = mk_eq2 wl env orig t1 t2  in
                               match uu____84122 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____84102 with
                          | (guard,wl1) ->
                              let uu____84143 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____84143))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____84146,uu____84147) ->
                  let head1 =
                    let uu____84155 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84155
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84201 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84201
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____84247 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____84247
                    then
                      let uu____84251 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____84253 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____84255 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____84251 uu____84253 uu____84255
                    else ());
                   (let no_free_uvars t =
                      (let uu____84269 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____84269) &&
                        (let uu____84273 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____84273)
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
                      let uu____84290 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____84290 = FStar_Syntax_Util.Equal  in
                    let uu____84291 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____84291
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____84295 = equal t1 t2  in
                         (if uu____84295
                          then
                            let uu____84298 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____84298
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____84303 =
                            let uu____84310 = equal t1 t2  in
                            if uu____84310
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____84323 = mk_eq2 wl env orig t1 t2  in
                               match uu____84323 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____84303 with
                          | (guard,wl1) ->
                              let uu____84344 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____84344))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____84347,uu____84348) ->
                  let head1 =
                    let uu____84350 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84350
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84396 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84396
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____84442 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____84442
                    then
                      let uu____84446 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____84448 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____84450 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____84446 uu____84448 uu____84450
                    else ());
                   (let no_free_uvars t =
                      (let uu____84464 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____84464) &&
                        (let uu____84468 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____84468)
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
                      let uu____84485 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____84485 = FStar_Syntax_Util.Equal  in
                    let uu____84486 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____84486
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____84490 = equal t1 t2  in
                         (if uu____84490
                          then
                            let uu____84493 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____84493
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____84498 =
                            let uu____84505 = equal t1 t2  in
                            if uu____84505
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____84518 = mk_eq2 wl env orig t1 t2  in
                               match uu____84518 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____84498 with
                          | (guard,wl1) ->
                              let uu____84539 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____84539))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____84542,uu____84543) ->
                  let head1 =
                    let uu____84545 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84545
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84591 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84591
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____84637 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____84637
                    then
                      let uu____84641 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____84643 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____84645 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____84641 uu____84643 uu____84645
                    else ());
                   (let no_free_uvars t =
                      (let uu____84659 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____84659) &&
                        (let uu____84663 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____84663)
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
                      let uu____84680 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____84680 = FStar_Syntax_Util.Equal  in
                    let uu____84681 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____84681
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____84685 = equal t1 t2  in
                         (if uu____84685
                          then
                            let uu____84688 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____84688
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____84693 =
                            let uu____84700 = equal t1 t2  in
                            if uu____84700
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____84713 = mk_eq2 wl env orig t1 t2  in
                               match uu____84713 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____84693 with
                          | (guard,wl1) ->
                              let uu____84734 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____84734))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____84737,uu____84738) ->
                  let head1 =
                    let uu____84740 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84740
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84786 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84786
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____84832 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____84832
                    then
                      let uu____84836 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____84838 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____84840 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____84836 uu____84838 uu____84840
                    else ());
                   (let no_free_uvars t =
                      (let uu____84854 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____84854) &&
                        (let uu____84858 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____84858)
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
                      let uu____84875 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____84875 = FStar_Syntax_Util.Equal  in
                    let uu____84876 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____84876
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____84880 = equal t1 t2  in
                         (if uu____84880
                          then
                            let uu____84883 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____84883
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____84888 =
                            let uu____84895 = equal t1 t2  in
                            if uu____84895
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____84908 = mk_eq2 wl env orig t1 t2  in
                               match uu____84908 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____84888 with
                          | (guard,wl1) ->
                              let uu____84929 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____84929))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____84932,uu____84933) ->
                  let head1 =
                    let uu____84951 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84951
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84997 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84997
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85043 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85043
                    then
                      let uu____85047 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85049 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85051 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85047 uu____85049 uu____85051
                    else ());
                   (let no_free_uvars t =
                      (let uu____85065 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85065) &&
                        (let uu____85069 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85069)
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
                      let uu____85086 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85086 = FStar_Syntax_Util.Equal  in
                    let uu____85087 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85087
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85091 = equal t1 t2  in
                         (if uu____85091
                          then
                            let uu____85094 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85094
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85099 =
                            let uu____85106 = equal t1 t2  in
                            if uu____85106
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85119 = mk_eq2 wl env orig t1 t2  in
                               match uu____85119 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85099 with
                          | (guard,wl1) ->
                              let uu____85140 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85140))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____85143,FStar_Syntax_Syntax.Tm_match uu____85144) ->
                  let head1 =
                    let uu____85168 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85168
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85214 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85214
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85260 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85260
                    then
                      let uu____85264 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85266 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85268 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85264 uu____85266 uu____85268
                    else ());
                   (let no_free_uvars t =
                      (let uu____85282 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85282) &&
                        (let uu____85286 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85286)
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
                      let uu____85303 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85303 = FStar_Syntax_Util.Equal  in
                    let uu____85304 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85304
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85308 = equal t1 t2  in
                         (if uu____85308
                          then
                            let uu____85311 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85311
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85316 =
                            let uu____85323 = equal t1 t2  in
                            if uu____85323
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85336 = mk_eq2 wl env orig t1 t2  in
                               match uu____85336 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85316 with
                          | (guard,wl1) ->
                              let uu____85357 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85357))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____85360,FStar_Syntax_Syntax.Tm_uinst uu____85361) ->
                  let head1 =
                    let uu____85369 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85369
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85409 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85409
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85449 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85449
                    then
                      let uu____85453 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85455 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85457 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85453 uu____85455 uu____85457
                    else ());
                   (let no_free_uvars t =
                      (let uu____85471 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85471) &&
                        (let uu____85475 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85475)
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
                      let uu____85492 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85492 = FStar_Syntax_Util.Equal  in
                    let uu____85493 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85493
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85497 = equal t1 t2  in
                         (if uu____85497
                          then
                            let uu____85500 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85500
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85505 =
                            let uu____85512 = equal t1 t2  in
                            if uu____85512
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85525 = mk_eq2 wl env orig t1 t2  in
                               match uu____85525 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85505 with
                          | (guard,wl1) ->
                              let uu____85546 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85546))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____85549,FStar_Syntax_Syntax.Tm_name uu____85550) ->
                  let head1 =
                    let uu____85552 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85552
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85592 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85592
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85632 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85632
                    then
                      let uu____85636 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85638 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85640 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85636 uu____85638 uu____85640
                    else ());
                   (let no_free_uvars t =
                      (let uu____85654 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85654) &&
                        (let uu____85658 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85658)
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
                      let uu____85675 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85675 = FStar_Syntax_Util.Equal  in
                    let uu____85676 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85676
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85680 = equal t1 t2  in
                         (if uu____85680
                          then
                            let uu____85683 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85683
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85688 =
                            let uu____85695 = equal t1 t2  in
                            if uu____85695
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85708 = mk_eq2 wl env orig t1 t2  in
                               match uu____85708 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85688 with
                          | (guard,wl1) ->
                              let uu____85729 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85729))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____85732,FStar_Syntax_Syntax.Tm_constant uu____85733) ->
                  let head1 =
                    let uu____85735 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85735
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85775 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85775
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85815 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85815
                    then
                      let uu____85819 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85821 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85823 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85819 uu____85821 uu____85823
                    else ());
                   (let no_free_uvars t =
                      (let uu____85837 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85837) &&
                        (let uu____85841 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85841)
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
                      let uu____85858 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85858 = FStar_Syntax_Util.Equal  in
                    let uu____85859 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85859
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85863 = equal t1 t2  in
                         (if uu____85863
                          then
                            let uu____85866 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85866
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85871 =
                            let uu____85878 = equal t1 t2  in
                            if uu____85878
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85891 = mk_eq2 wl env orig t1 t2  in
                               match uu____85891 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85871 with
                          | (guard,wl1) ->
                              let uu____85912 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85912))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____85915,FStar_Syntax_Syntax.Tm_fvar uu____85916) ->
                  let head1 =
                    let uu____85918 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85918
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85958 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85958
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85998 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85998
                    then
                      let uu____86002 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____86004 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____86006 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____86002 uu____86004 uu____86006
                    else ());
                   (let no_free_uvars t =
                      (let uu____86020 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____86020) &&
                        (let uu____86024 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____86024)
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
                      let uu____86041 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____86041 = FStar_Syntax_Util.Equal  in
                    let uu____86042 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____86042
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____86046 = equal t1 t2  in
                         (if uu____86046
                          then
                            let uu____86049 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____86049
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____86054 =
                            let uu____86061 = equal t1 t2  in
                            if uu____86061
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____86074 = mk_eq2 wl env orig t1 t2  in
                               match uu____86074 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____86054 with
                          | (guard,wl1) ->
                              let uu____86095 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____86095))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____86098,FStar_Syntax_Syntax.Tm_app uu____86099) ->
                  let head1 =
                    let uu____86117 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____86117
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____86157 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____86157
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____86197 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____86197
                    then
                      let uu____86201 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____86203 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____86205 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____86201 uu____86203 uu____86205
                    else ());
                   (let no_free_uvars t =
                      (let uu____86219 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____86219) &&
                        (let uu____86223 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____86223)
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
                      let uu____86240 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____86240 = FStar_Syntax_Util.Equal  in
                    let uu____86241 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____86241
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____86245 = equal t1 t2  in
                         (if uu____86245
                          then
                            let uu____86248 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____86248
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____86253 =
                            let uu____86260 = equal t1 t2  in
                            if uu____86260
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____86273 = mk_eq2 wl env orig t1 t2  in
                               match uu____86273 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____86253 with
                          | (guard,wl1) ->
                              let uu____86294 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____86294))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____86297,FStar_Syntax_Syntax.Tm_let uu____86298) ->
                  let uu____86325 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____86325
                  then
                    let uu____86328 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____86328
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____86332,uu____86333) ->
                  let uu____86347 =
                    let uu____86353 =
                      let uu____86355 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____86357 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____86359 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____86361 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____86355 uu____86357 uu____86359 uu____86361
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____86353)
                     in
                  FStar_Errors.raise_error uu____86347
                    t1.FStar_Syntax_Syntax.pos
              | (uu____86365,FStar_Syntax_Syntax.Tm_let uu____86366) ->
                  let uu____86380 =
                    let uu____86386 =
                      let uu____86388 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____86390 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____86392 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____86394 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____86388 uu____86390 uu____86392 uu____86394
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____86386)
                     in
                  FStar_Errors.raise_error uu____86380
                    t1.FStar_Syntax_Syntax.pos
              | uu____86398 -> giveup env "head tag mismatch" orig))))

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
          (let uu____86462 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____86462
           then
             let uu____86467 =
               let uu____86469 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____86469  in
             let uu____86470 =
               let uu____86472 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____86472  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____86467 uu____86470
           else ());
          (let uu____86476 =
             let uu____86478 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____86478  in
           if uu____86476
           then
             let uu____86481 =
               let uu____86483 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____86485 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____86483 uu____86485
                in
             giveup env uu____86481 orig
           else
             (let uu____86490 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____86490 with
              | (ret_sub_prob,wl1) ->
                  let uu____86498 =
                    FStar_List.fold_right2
                      (fun uu____86535  ->
                         fun uu____86536  ->
                           fun uu____86537  ->
                             match (uu____86535, uu____86536, uu____86537)
                             with
                             | ((a1,uu____86581),(a2,uu____86583),(arg_sub_probs,wl2))
                                 ->
                                 let uu____86616 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____86616 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____86498 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____86646 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____86646  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____86654 = attempt sub_probs wl3  in
                       solve env uu____86654)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____86677 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____86680)::[] -> wp1
              | uu____86705 ->
                  let uu____86716 =
                    let uu____86718 =
                      let uu____86720 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____86720  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____86718
                     in
                  failwith uu____86716
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____86727 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____86727]
              | x -> x  in
            let uu____86729 =
              let uu____86740 =
                let uu____86749 =
                  let uu____86750 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____86750 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____86749  in
              [uu____86740]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____86729;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____86768 = lift_c1 ()  in solve_eq uu____86768 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___616_86777  ->
                       match uu___616_86777 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____86782 -> false))
                in
             let uu____86784 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____86814)::uu____86815,(wp2,uu____86817)::uu____86818)
                   -> (wp1, wp2)
               | uu____86891 ->
                   let uu____86916 =
                     let uu____86922 =
                       let uu____86924 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____86926 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____86924 uu____86926
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____86922)
                      in
                   FStar_Errors.raise_error uu____86916
                     env.FStar_TypeChecker_Env.range
                in
             match uu____86784 with
             | (wpc1,wpc2) ->
                 let uu____86936 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____86936
                 then
                   let uu____86941 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____86941 wl
                 else
                   (let uu____86945 =
                      let uu____86952 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____86952  in
                    match uu____86945 with
                    | (c2_decl,qualifiers) ->
                        let uu____86973 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____86973
                        then
                          let c1_repr =
                            let uu____86980 =
                              let uu____86981 =
                                let uu____86982 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____86982  in
                              let uu____86983 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____86981 uu____86983
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____86980
                             in
                          let c2_repr =
                            let uu____86985 =
                              let uu____86986 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____86987 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____86986 uu____86987
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____86985
                             in
                          let uu____86988 =
                            let uu____86993 =
                              let uu____86995 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____86997 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____86995 uu____86997
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____86993
                             in
                          (match uu____86988 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____87003 = attempt [prob] wl2  in
                               solve env uu____87003)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____87018 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____87018
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____87027 =
                                     let uu____87034 =
                                       let uu____87035 =
                                         let uu____87052 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____87055 =
                                           let uu____87066 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____87075 =
                                             let uu____87086 =
                                               let uu____87095 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____87095
                                                in
                                             [uu____87086]  in
                                           uu____87066 :: uu____87075  in
                                         (uu____87052, uu____87055)  in
                                       FStar_Syntax_Syntax.Tm_app uu____87035
                                        in
                                     FStar_Syntax_Syntax.mk uu____87034  in
                                   uu____87027 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____87144 =
                                    let uu____87151 =
                                      let uu____87152 =
                                        let uu____87169 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____87172 =
                                          let uu____87183 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____87192 =
                                            let uu____87203 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____87212 =
                                              let uu____87223 =
                                                let uu____87232 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____87232
                                                 in
                                              [uu____87223]  in
                                            uu____87203 :: uu____87212  in
                                          uu____87183 :: uu____87192  in
                                        (uu____87169, uu____87172)  in
                                      FStar_Syntax_Syntax.Tm_app uu____87152
                                       in
                                    FStar_Syntax_Syntax.mk uu____87151  in
                                  uu____87144 FStar_Pervasives_Native.None r)
                              in
                           (let uu____87286 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____87286
                            then
                              let uu____87291 =
                                let uu____87293 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____87293
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____87291
                            else ());
                           (let uu____87297 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____87297 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____87306 =
                                    let uu____87309 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _87312  ->
                                         FStar_Pervasives_Native.Some _87312)
                                      uu____87309
                                     in
                                  solve_prob orig uu____87306 [] wl1  in
                                let uu____87313 = attempt [base_prob] wl2  in
                                solve env uu____87313))))
           in
        let uu____87314 = FStar_Util.physical_equality c1 c2  in
        if uu____87314
        then
          let uu____87317 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____87317
        else
          ((let uu____87321 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____87321
            then
              let uu____87326 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____87328 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____87326
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____87328
            else ());
           (let uu____87333 =
              let uu____87342 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____87345 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____87342, uu____87345)  in
            match uu____87333 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____87363),FStar_Syntax_Syntax.Total
                    (t2,uu____87365)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____87382 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____87382 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____87384,FStar_Syntax_Syntax.Total uu____87385) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____87404),FStar_Syntax_Syntax.Total
                    (t2,uu____87406)) ->
                     let uu____87423 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____87423 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____87426),FStar_Syntax_Syntax.GTotal
                    (t2,uu____87428)) ->
                     let uu____87445 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____87445 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____87448),FStar_Syntax_Syntax.GTotal
                    (t2,uu____87450)) ->
                     let uu____87467 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____87467 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____87469,FStar_Syntax_Syntax.Comp uu____87470) ->
                     let uu____87479 =
                       let uu___4158_87482 = problem  in
                       let uu____87485 =
                         let uu____87486 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____87486
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4158_87482.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____87485;
                         FStar_TypeChecker_Common.relation =
                           (uu___4158_87482.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___4158_87482.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___4158_87482.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4158_87482.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4158_87482.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4158_87482.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4158_87482.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4158_87482.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____87479 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____87487,FStar_Syntax_Syntax.Comp uu____87488) ->
                     let uu____87497 =
                       let uu___4158_87500 = problem  in
                       let uu____87503 =
                         let uu____87504 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____87504
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4158_87500.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____87503;
                         FStar_TypeChecker_Common.relation =
                           (uu___4158_87500.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___4158_87500.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___4158_87500.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4158_87500.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4158_87500.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4158_87500.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4158_87500.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4158_87500.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____87497 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____87505,FStar_Syntax_Syntax.GTotal uu____87506) ->
                     let uu____87515 =
                       let uu___4170_87518 = problem  in
                       let uu____87521 =
                         let uu____87522 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____87522
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4170_87518.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___4170_87518.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___4170_87518.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____87521;
                         FStar_TypeChecker_Common.element =
                           (uu___4170_87518.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4170_87518.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4170_87518.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4170_87518.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4170_87518.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4170_87518.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____87515 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____87523,FStar_Syntax_Syntax.Total uu____87524) ->
                     let uu____87533 =
                       let uu___4170_87536 = problem  in
                       let uu____87539 =
                         let uu____87540 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____87540
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4170_87536.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___4170_87536.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___4170_87536.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____87539;
                         FStar_TypeChecker_Common.element =
                           (uu___4170_87536.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4170_87536.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4170_87536.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4170_87536.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4170_87536.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4170_87536.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____87533 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____87541,FStar_Syntax_Syntax.Comp uu____87542) ->
                     let uu____87543 =
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
                     if uu____87543
                     then
                       let uu____87546 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____87546 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____87553 =
                            let uu____87558 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____87558
                            then (c1_comp, c2_comp)
                            else
                              (let uu____87567 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____87568 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____87567, uu____87568))
                             in
                          match uu____87553 with
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
                           (let uu____87576 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____87576
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____87584 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____87584 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____87587 =
                                  let uu____87589 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____87591 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____87589 uu____87591
                                   in
                                giveup env uu____87587 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____87602 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____87602 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____87652 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____87652 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____87677 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____87708  ->
                match uu____87708 with
                | (u1,u2) ->
                    let uu____87716 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____87718 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____87716 uu____87718))
         in
      FStar_All.pipe_right uu____87677 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____87755,[])) when
          let uu____87782 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____87782 -> "{}"
      | uu____87785 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____87812 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____87812
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____87824 =
              FStar_List.map
                (fun uu____87837  ->
                   match uu____87837 with
                   | (uu____87844,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____87824 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____87855 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____87855 imps
  
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
                  let uu____87912 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____87912
                  then
                    let uu____87920 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____87922 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____87920
                      (rel_to_string rel) uu____87922
                  else "TOP"  in
                let uu____87928 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____87928 with
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
              let uu____87988 =
                let uu____87991 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _87994  -> FStar_Pervasives_Native.Some _87994)
                  uu____87991
                 in
              FStar_Syntax_Syntax.new_bv uu____87988 t1  in
            let uu____87995 =
              let uu____88000 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____88000
               in
            match uu____87995 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____88060 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____88060
         then
           let uu____88065 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____88065
         else ());
        (let uu____88072 =
           FStar_Util.record_time (fun uu____88079  -> solve env probs)  in
         match uu____88072 with
         | (sol,ms) ->
             ((let uu____88091 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____88091
               then
                 let uu____88096 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____88096
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____88109 =
                     FStar_Util.record_time
                       (fun uu____88116  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____88109 with
                    | ((),ms1) ->
                        ((let uu____88127 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____88127
                          then
                            let uu____88132 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____88132
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____88146 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____88146
                     then
                       let uu____88153 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____88153
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
          ((let uu____88180 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____88180
            then
              let uu____88185 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____88185
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____88192 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____88192
             then
               let uu____88197 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____88197
             else ());
            (let f2 =
               let uu____88203 =
                 let uu____88204 = FStar_Syntax_Util.unmeta f1  in
                 uu____88204.FStar_Syntax_Syntax.n  in
               match uu____88203 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____88208 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___4286_88209 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___4286_88209.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___4286_88209.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___4286_88209.FStar_TypeChecker_Env.implicits)
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
            let uu____88264 =
              let uu____88265 =
                let uu____88266 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _88267  ->
                       FStar_TypeChecker_Common.NonTrivial _88267)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____88266;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____88265  in
            FStar_All.pipe_left
              (fun _88274  -> FStar_Pervasives_Native.Some _88274)
              uu____88264
  
let with_guard_no_simp :
  'Auu____88284 .
    'Auu____88284 ->
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
            let uu____88307 =
              let uu____88308 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _88309  -> FStar_TypeChecker_Common.NonTrivial _88309)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____88308;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____88307
  
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
          (let uu____88342 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____88342
           then
             let uu____88347 = FStar_Syntax_Print.term_to_string t1  in
             let uu____88349 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____88347
               uu____88349
           else ());
          (let uu____88354 =
             let uu____88359 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____88359
              in
           match uu____88354 with
           | (prob,wl) ->
               let g =
                 let uu____88367 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____88377  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____88367  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____88413 = try_teq true env t1 t2  in
        match uu____88413 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____88418 = FStar_TypeChecker_Env.get_range env  in
              let uu____88419 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____88418 uu____88419);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____88427 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____88427
              then
                let uu____88432 = FStar_Syntax_Print.term_to_string t1  in
                let uu____88434 = FStar_Syntax_Print.term_to_string t2  in
                let uu____88436 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____88432
                  uu____88434 uu____88436
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
          let uu____88462 = FStar_TypeChecker_Env.get_range env  in
          let uu____88463 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____88462 uu____88463
  
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
        (let uu____88492 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____88492
         then
           let uu____88497 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____88499 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____88497 uu____88499
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____88510 =
           let uu____88517 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____88517 "sub_comp"
            in
         match uu____88510 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____88530 =
                 FStar_Util.record_time
                   (fun uu____88542  ->
                      let uu____88543 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____88554  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____88543)
                  in
               match uu____88530 with
               | (r,ms) ->
                   ((let uu____88585 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____88585
                     then
                       let uu____88590 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____88592 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____88594 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____88590 uu____88592
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____88594
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
      fun uu____88632  ->
        match uu____88632 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____88675 =
                 let uu____88681 =
                   let uu____88683 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____88685 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____88683 uu____88685
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____88681)  in
               let uu____88689 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____88675 uu____88689)
               in
            let equiv1 v1 v' =
              let uu____88702 =
                let uu____88707 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____88708 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____88707, uu____88708)  in
              match uu____88702 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____88728 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____88759 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____88759 with
                      | FStar_Syntax_Syntax.U_unif uu____88766 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____88795  ->
                                    match uu____88795 with
                                    | (u,v') ->
                                        let uu____88804 = equiv1 v1 v'  in
                                        if uu____88804
                                        then
                                          let uu____88809 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____88809 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____88830 -> []))
               in
            let uu____88835 =
              let wl =
                let uu___4377_88839 = empty_worklist env  in
                {
                  attempting = (uu___4377_88839.attempting);
                  wl_deferred = (uu___4377_88839.wl_deferred);
                  ctr = (uu___4377_88839.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4377_88839.smt_ok);
                  umax_heuristic_ok = (uu___4377_88839.umax_heuristic_ok);
                  tcenv = (uu___4377_88839.tcenv);
                  wl_implicits = (uu___4377_88839.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____88858  ->
                      match uu____88858 with
                      | (lb,v1) ->
                          let uu____88865 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____88865 with
                           | USolved wl1 -> ()
                           | uu____88868 -> fail1 lb v1)))
               in
            let rec check_ineq uu____88879 =
              match uu____88879 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____88891) -> true
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
                      uu____88915,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____88917,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____88928) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____88936,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____88945 -> false)
               in
            let uu____88951 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____88968  ->
                      match uu____88968 with
                      | (u,v1) ->
                          let uu____88976 = check_ineq (u, v1)  in
                          if uu____88976
                          then true
                          else
                            ((let uu____88984 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____88984
                              then
                                let uu____88989 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____88991 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____88989
                                  uu____88991
                              else ());
                             false)))
               in
            if uu____88951
            then ()
            else
              ((let uu____89001 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____89001
                then
                  ((let uu____89007 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____89007);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____89019 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____89019))
                else ());
               (let uu____89032 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____89032))
  
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
        let fail1 uu____89106 =
          match uu____89106 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4454_89132 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___4454_89132.attempting);
            wl_deferred = (uu___4454_89132.wl_deferred);
            ctr = (uu___4454_89132.ctr);
            defer_ok;
            smt_ok = (uu___4454_89132.smt_ok);
            umax_heuristic_ok = (uu___4454_89132.umax_heuristic_ok);
            tcenv = (uu___4454_89132.tcenv);
            wl_implicits = (uu___4454_89132.wl_implicits)
          }  in
        (let uu____89135 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____89135
         then
           let uu____89140 = FStar_Util.string_of_bool defer_ok  in
           let uu____89142 = wl_to_string wl  in
           let uu____89144 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____89140 uu____89142 uu____89144
         else ());
        (let g1 =
           let uu____89150 = solve_and_commit env wl fail1  in
           match uu____89150 with
           | FStar_Pervasives_Native.Some
               (uu____89157::uu____89158,uu____89159) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4469_89188 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___4469_89188.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___4469_89188.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____89189 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___4474_89198 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4474_89198.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4474_89198.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___4474_89198.FStar_TypeChecker_Env.implicits)
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
    let uu____89241 = FStar_ST.op_Bang last_proof_ns  in
    match uu____89241 with
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
            let uu___4493_89366 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___4493_89366.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___4493_89366.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___4493_89366.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____89367 =
            let uu____89369 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____89369  in
          if uu____89367
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____89381 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____89382 =
                       let uu____89384 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____89384
                        in
                     FStar_Errors.diag uu____89381 uu____89382)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____89392 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____89393 =
                        let uu____89395 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____89395
                         in
                      FStar_Errors.diag uu____89392 uu____89393)
                   else ();
                   (let uu____89401 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____89401
                      "discharge_guard'" env vc1);
                   (let uu____89403 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____89403 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____89412 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____89413 =
                                let uu____89415 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____89415
                                 in
                              FStar_Errors.diag uu____89412 uu____89413)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____89425 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____89426 =
                                let uu____89428 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____89428
                                 in
                              FStar_Errors.diag uu____89425 uu____89426)
                           else ();
                           (let vcs =
                              let uu____89442 = FStar_Options.use_tactics ()
                                 in
                              if uu____89442
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____89464  ->
                                     (let uu____89466 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____89466);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____89510  ->
                                              match uu____89510 with
                                              | (env1,goal,opts) ->
                                                  let uu____89526 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____89526, opts)))))
                              else
                                (let uu____89529 =
                                   let uu____89536 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____89536)  in
                                 [uu____89529])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____89569  ->
                                    match uu____89569 with
                                    | (env1,goal,opts) ->
                                        let uu____89579 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____89579 with
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
                                                (let uu____89591 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____89592 =
                                                   let uu____89594 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____89596 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____89594 uu____89596
                                                    in
                                                 FStar_Errors.diag
                                                   uu____89591 uu____89592)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____89603 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____89604 =
                                                   let uu____89606 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____89606
                                                    in
                                                 FStar_Errors.diag
                                                   uu____89603 uu____89604)
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
      let uu____89624 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____89624 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____89633 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____89633
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____89647 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____89647 with
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
        let uu____89677 = try_teq false env t1 t2  in
        match uu____89677 with
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
            let uu____89721 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____89721 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____89734 ->
                     let uu____89747 =
                       let uu____89748 = FStar_Syntax_Subst.compress r  in
                       uu____89748.FStar_Syntax_Syntax.n  in
                     (match uu____89747 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____89753) ->
                          unresolved ctx_u'
                      | uu____89770 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____89794 = acc  in
            match uu____89794 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____89813 = hd1  in
                     (match uu____89813 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____89824 = unresolved ctx_u  in
                             if uu____89824
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____89848 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____89848
                                     then
                                       let uu____89852 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____89852
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____89861 = teq_nosmt env1 t tm
                                          in
                                       match uu____89861 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Env.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4606_89871 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4606_89871.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4606_89871.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4606_89871.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4606_89871.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4606_89871.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4606_89871.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4606_89871.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4609_89879 = hd1  in
                                       {
                                         FStar_TypeChecker_Env.imp_reason =
                                           (uu___4609_89879.FStar_TypeChecker_Env.imp_reason);
                                         FStar_TypeChecker_Env.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Env.imp_tm =
                                           (uu___4609_89879.FStar_TypeChecker_Env.imp_tm);
                                         FStar_TypeChecker_Env.imp_range =
                                           (uu___4609_89879.FStar_TypeChecker_Env.imp_range)
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
                                    let uu___4613_89890 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4613_89890.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4613_89890.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4613_89890.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4613_89890.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4613_89890.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4613_89890.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4613_89890.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4613_89890.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4613_89890.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___4613_89890.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4613_89890.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4613_89890.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4613_89890.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4613_89890.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4613_89890.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4613_89890.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4613_89890.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4613_89890.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4613_89890.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4613_89890.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4613_89890.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4613_89890.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4613_89890.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4613_89890.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4613_89890.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4613_89890.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4613_89890.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4613_89890.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4613_89890.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4613_89890.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4613_89890.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4613_89890.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4613_89890.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4613_89890.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4613_89890.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4613_89890.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4613_89890.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4613_89890.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4613_89890.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4613_89890.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4613_89890.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4613_89890.FStar_TypeChecker_Env.nbe)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4618_89894 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4618_89894.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4618_89894.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4618_89894.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4618_89894.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4618_89894.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4618_89894.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4618_89894.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4618_89894.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4618_89894.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4618_89894.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___4618_89894.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4618_89894.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4618_89894.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4618_89894.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4618_89894.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4618_89894.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4618_89894.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4618_89894.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4618_89894.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4618_89894.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4618_89894.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4618_89894.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4618_89894.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4618_89894.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4618_89894.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4618_89894.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4618_89894.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4618_89894.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4618_89894.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4618_89894.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4618_89894.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4618_89894.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4618_89894.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4618_89894.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4618_89894.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4618_89894.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4618_89894.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4618_89894.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4618_89894.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4618_89894.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4618_89894.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4618_89894.FStar_TypeChecker_Env.nbe)
                                      }
                                    else env1  in
                                  (let uu____89899 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____89899
                                   then
                                     let uu____89904 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____89906 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____89908 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____89910 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____89904 uu____89906 uu____89908
                                       reason uu____89910
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4624_89917  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____89924 =
                                             let uu____89934 =
                                               let uu____89942 =
                                                 let uu____89944 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____89946 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____89948 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____89944 uu____89946
                                                   uu____89948
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____89942, r)
                                                in
                                             [uu____89934]  in
                                           FStar_Errors.add_errors
                                             uu____89924);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___4632_89968 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___4632_89968.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___4632_89968.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___4632_89968.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____89972 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____89983  ->
                                               let uu____89984 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____89986 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____89988 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____89984 uu____89986
                                                 reason uu____89988)) env2 g2
                                         true
                                        in
                                     match uu____89972 with
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
          let uu___4640_89996 = g  in
          let uu____89997 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4640_89996.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4640_89996.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___4640_89996.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____89997
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
        let uu____90040 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____90040 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____90041 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____90041
      | imp::uu____90043 ->
          let uu____90046 =
            let uu____90052 =
              let uu____90054 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____90056 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____90054 uu____90056 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____90052)
             in
          FStar_Errors.raise_error uu____90046
            imp.FStar_TypeChecker_Env.imp_range
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____90078 = teq_nosmt env t1 t2  in
        match uu____90078 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4662_90097 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___4662_90097.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___4662_90097.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___4662_90097.FStar_TypeChecker_Env.implicits)
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
        (let uu____90133 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____90133
         then
           let uu____90138 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____90140 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____90138
             uu____90140
         else ());
        (let uu____90145 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____90145 with
         | (prob,x,wl) ->
             let g =
               let uu____90164 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____90175  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____90164  in
             ((let uu____90196 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____90196
               then
                 let uu____90201 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____90203 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____90205 =
                   let uu____90207 = FStar_Util.must g  in
                   guard_to_string env uu____90207  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____90201 uu____90203 uu____90205
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
        let uu____90244 = check_subtyping env t1 t2  in
        match uu____90244 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____90263 =
              let uu____90264 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____90264 g  in
            FStar_Pervasives_Native.Some uu____90263
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____90283 = check_subtyping env t1 t2  in
        match uu____90283 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____90302 =
              let uu____90303 =
                let uu____90304 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____90304]  in
              FStar_TypeChecker_Env.close_guard env uu____90303 g  in
            FStar_Pervasives_Native.Some uu____90302
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____90342 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____90342
         then
           let uu____90347 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____90349 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____90347
             uu____90349
         else ());
        (let uu____90354 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____90354 with
         | (prob,x,wl) ->
             let g =
               let uu____90369 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____90380  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____90369  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____90404 =
                      let uu____90405 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____90405]  in
                    FStar_TypeChecker_Env.close_guard env uu____90404 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____90446 = subtype_nosmt env t1 t2  in
        match uu____90446 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  