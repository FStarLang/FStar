open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____60298 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____60333 -> false
  
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
                    let uu____60756 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____60756;
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
                     (let uu___656_60788 = wl  in
                      {
                        attempting = (uu___656_60788.attempting);
                        wl_deferred = (uu___656_60788.wl_deferred);
                        ctr = (uu___656_60788.ctr);
                        defer_ok = (uu___656_60788.defer_ok);
                        smt_ok = (uu___656_60788.smt_ok);
                        umax_heuristic_ok =
                          (uu___656_60788.umax_heuristic_ok);
                        tcenv = (uu___656_60788.tcenv);
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
            let uu___662_60821 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___662_60821.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___662_60821.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___662_60821.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___662_60821.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___662_60821.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___662_60821.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___662_60821.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___662_60821.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___662_60821.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___662_60821.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___662_60821.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___662_60821.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___662_60821.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___662_60821.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___662_60821.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___662_60821.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___662_60821.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___662_60821.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___662_60821.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___662_60821.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___662_60821.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___662_60821.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___662_60821.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___662_60821.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___662_60821.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___662_60821.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___662_60821.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___662_60821.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___662_60821.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___662_60821.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___662_60821.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___662_60821.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___662_60821.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___662_60821.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___662_60821.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___662_60821.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___662_60821.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___662_60821.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___662_60821.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___662_60821.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___662_60821.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___662_60821.FStar_TypeChecker_Env.nbe)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____60823 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____60823 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Env.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * Prims.string) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____60866 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____60902 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * Prims.string)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____60935 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____60946 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____60957 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___585_60975  ->
    match uu___585_60975 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____60987 = FStar_Syntax_Util.head_and_args t  in
    match uu____60987 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____61050 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____61052 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____61067 =
                     let uu____61069 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____61069  in
                   FStar_Util.format1 "@<%s>" uu____61067
                in
             let uu____61073 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____61050 uu____61052 uu____61073
         | uu____61076 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___586_61088  ->
      match uu___586_61088 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____61093 =
            let uu____61097 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____61099 =
              let uu____61103 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____61105 =
                let uu____61109 =
                  let uu____61113 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____61113]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____61109
                 in
              uu____61103 :: uu____61105  in
            uu____61097 :: uu____61099  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____61093
      | FStar_TypeChecker_Common.CProb p ->
          let uu____61124 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____61126 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____61128 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____61124
            uu____61126 (rel_to_string p.FStar_TypeChecker_Common.relation)
            uu____61128
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___587_61142  ->
      match uu___587_61142 with
      | UNIV (u,t) ->
          let x =
            let uu____61148 = FStar_Options.hide_uvar_nums ()  in
            if uu____61148
            then "?"
            else
              (let uu____61155 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____61155 FStar_Util.string_of_int)
             in
          let uu____61159 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____61159
      | TERM (u,t) ->
          let x =
            let uu____61166 = FStar_Options.hide_uvar_nums ()  in
            if uu____61166
            then "?"
            else
              (let uu____61173 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____61173 FStar_Util.string_of_int)
             in
          let uu____61177 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____61177
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____61196 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____61196 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____61217 =
      let uu____61221 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____61221
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____61217 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____61240 .
    (FStar_Syntax_Syntax.term * 'Auu____61240) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____61259 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____61280  ->
              match uu____61280 with
              | (x,uu____61287) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____61259 (FStar_String.concat " ")
  
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
        (let uu____61330 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____61330
         then
           let uu____61335 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____61335
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___588_61346  ->
    match uu___588_61346 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____61352 .
    'Auu____61352 FStar_TypeChecker_Common.problem ->
      'Auu____61352 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___722_61364 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___722_61364.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___722_61364.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___722_61364.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___722_61364.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___722_61364.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___722_61364.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___722_61364.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____61372 .
    'Auu____61372 FStar_TypeChecker_Common.problem ->
      'Auu____61372 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___589_61392  ->
    match uu___589_61392 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _61398  -> FStar_TypeChecker_Common.TProb _61398)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _61404  -> FStar_TypeChecker_Common.CProb _61404)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___590_61410  ->
    match uu___590_61410 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___734_61416 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___734_61416.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___734_61416.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___734_61416.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___734_61416.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___734_61416.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___734_61416.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___734_61416.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___734_61416.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___734_61416.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___738_61424 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___738_61424.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___738_61424.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___738_61424.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___738_61424.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___738_61424.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___738_61424.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___738_61424.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___738_61424.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___738_61424.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___591_61437  ->
      match uu___591_61437 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___592_61444  ->
    match uu___592_61444 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___593_61457  ->
    match uu___593_61457 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___594_61472  ->
    match uu___594_61472 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___595_61487  ->
    match uu___595_61487 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___596_61501  ->
    match uu___596_61501 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___597_61515  ->
    match uu___597_61515 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___598_61527  ->
    match uu___598_61527 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____61543 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____61543) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____61573 =
          let uu____61575 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____61575  in
        if uu____61573
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____61612)::bs ->
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
          let uu____61659 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____61683 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____61683]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____61659
      | FStar_TypeChecker_Common.CProb p ->
          let uu____61711 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____61735 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____61735]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____61711
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____61782 =
          let uu____61784 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____61784  in
        if uu____61782
        then ()
        else
          (let uu____61789 =
             let uu____61792 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____61792
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____61789 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____61841 =
          let uu____61843 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____61843  in
        if uu____61841
        then ()
        else
          (let uu____61848 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____61848)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____61868 =
        let uu____61870 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____61870  in
      if uu____61868
      then ()
      else
        (let msgf m =
           let uu____61884 =
             let uu____61886 =
               let uu____61888 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____61888 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____61886  in
           Prims.op_Hat msg uu____61884  in
         (let uu____61893 = msgf "scope"  in
          let uu____61896 = p_scope prob  in
          def_scope_wf uu____61893 (p_loc prob) uu____61896);
         (let uu____61908 = msgf "guard"  in
          def_check_scoped uu____61908 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____61915 = msgf "lhs"  in
                def_check_scoped uu____61915 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____61918 = msgf "rhs"  in
                def_check_scoped uu____61918 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____61925 = msgf "lhs"  in
                def_check_scoped_comp uu____61925 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____61928 = msgf "rhs"  in
                def_check_scoped_comp uu____61928 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___831_61949 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___831_61949.wl_deferred);
          ctr = (uu___831_61949.ctr);
          defer_ok = (uu___831_61949.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___831_61949.umax_heuristic_ok);
          tcenv = (uu___831_61949.tcenv);
          wl_implicits = (uu___831_61949.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____61957 .
    FStar_TypeChecker_Env.env ->
      ('Auu____61957 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___835_61980 = empty_worklist env  in
      let uu____61981 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____61981;
        wl_deferred = (uu___835_61980.wl_deferred);
        ctr = (uu___835_61980.ctr);
        defer_ok = (uu___835_61980.defer_ok);
        smt_ok = (uu___835_61980.smt_ok);
        umax_heuristic_ok = (uu___835_61980.umax_heuristic_ok);
        tcenv = (uu___835_61980.tcenv);
        wl_implicits = (uu___835_61980.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___840_62004 = wl  in
        {
          attempting = (uu___840_62004.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___840_62004.ctr);
          defer_ok = (uu___840_62004.defer_ok);
          smt_ok = (uu___840_62004.smt_ok);
          umax_heuristic_ok = (uu___840_62004.umax_heuristic_ok);
          tcenv = (uu___840_62004.tcenv);
          wl_implicits = (uu___840_62004.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___845_62032 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___845_62032.wl_deferred);
         ctr = (uu___845_62032.ctr);
         defer_ok = (uu___845_62032.defer_ok);
         smt_ok = (uu___845_62032.smt_ok);
         umax_heuristic_ok = (uu___845_62032.umax_heuristic_ok);
         tcenv = (uu___845_62032.tcenv);
         wl_implicits = (uu___845_62032.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____62046 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____62046 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____62080 = FStar_Syntax_Util.type_u ()  in
            match uu____62080 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____62092 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____62092 with
                 | (uu____62110,tt,wl1) ->
                     let uu____62113 = FStar_Syntax_Util.mk_eq2 u tt t1 t2
                        in
                     (uu____62113, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___599_62119  ->
    match uu___599_62119 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _62125  -> FStar_TypeChecker_Common.TProb _62125) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _62131  -> FStar_TypeChecker_Common.CProb _62131) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____62139 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____62139 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____62159  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____62201 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____62201 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____62201 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____62201 FStar_TypeChecker_Common.problem *
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
                        let uu____62288 =
                          let uu____62297 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____62297]  in
                        FStar_List.append scope uu____62288
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____62340 =
                      let uu____62343 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____62343  in
                    FStar_List.append uu____62340
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____62362 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____62362 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____62388 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____62388;
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
                  (let uu____62462 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____62462 with
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
                  (let uu____62550 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____62550 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____62588 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____62588 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____62588 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____62588 FStar_TypeChecker_Common.problem *
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
                          let uu____62656 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____62656]  in
                        let uu____62675 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____62675
                     in
                  let uu____62678 =
                    let uu____62685 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___928_62696 = wl  in
                       {
                         attempting = (uu___928_62696.attempting);
                         wl_deferred = (uu___928_62696.wl_deferred);
                         ctr = (uu___928_62696.ctr);
                         defer_ok = (uu___928_62696.defer_ok);
                         smt_ok = (uu___928_62696.smt_ok);
                         umax_heuristic_ok =
                           (uu___928_62696.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___928_62696.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____62685
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____62678 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____62714 =
                              let uu____62719 =
                                let uu____62720 =
                                  let uu____62729 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____62729
                                   in
                                [uu____62720]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____62719
                               in
                            uu____62714 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____62757 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____62757;
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
                let uu____62805 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____62805;
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
  'Auu____62820 .
    worklist ->
      'Auu____62820 FStar_TypeChecker_Common.problem ->
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
              let uu____62853 =
                let uu____62856 =
                  let uu____62857 =
                    let uu____62864 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____62864)  in
                  FStar_Syntax_Syntax.NT uu____62857  in
                [uu____62856]  in
              FStar_Syntax_Subst.subst uu____62853 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____62888 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____62888
        then
          let uu____62896 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____62899 = prob_to_string env d  in
          let uu____62901 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____62896 uu____62899 uu____62901 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____62917 -> failwith "impossible"  in
           let uu____62920 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____62936 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____62938 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____62936, uu____62938)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____62945 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____62947 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____62945, uu____62947)
              in
           match uu____62920 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___600_62975  ->
            match uu___600_62975 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____62987 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____62991 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____62991 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___601_63022  ->
           match uu___601_63022 with
           | UNIV uu____63025 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____63032 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____63032
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
        (fun uu___602_63060  ->
           match uu___602_63060 with
           | UNIV (u',t) ->
               let uu____63065 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____63065
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____63072 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____63084 =
        let uu____63085 =
          let uu____63086 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____63086
           in
        FStar_Syntax_Subst.compress uu____63085  in
      FStar_All.pipe_right uu____63084 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____63098 =
        let uu____63099 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____63099  in
      FStar_All.pipe_right uu____63098 FStar_Syntax_Util.unlazy_emb
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____63107 = FStar_Syntax_Util.head_and_args t  in
    match uu____63107 with
    | (h,uu____63126) ->
        let uu____63151 =
          let uu____63152 = FStar_Syntax_Subst.compress h  in
          uu____63152.FStar_Syntax_Syntax.n  in
        (match uu____63151 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____63157 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____63170 = should_strongly_reduce t  in
      if uu____63170
      then
        let uu____63173 =
          let uu____63174 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Reify;
              FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant] env t
             in
          FStar_Syntax_Subst.compress uu____63174  in
        FStar_All.pipe_right uu____63173 FStar_Syntax_Util.unlazy_emb
      else whnf' env t
  
let norm_arg :
  'Auu____63184 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____63184) ->
        (FStar_Syntax_Syntax.term * 'Auu____63184)
  =
  fun env  ->
    fun t  ->
      let uu____63207 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____63207, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____63259  ->
              match uu____63259 with
              | (x,imp) ->
                  let uu____63278 =
                    let uu___1025_63279 = x  in
                    let uu____63280 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1025_63279.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1025_63279.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____63280
                    }  in
                  (uu____63278, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____63304 = aux u3  in
            FStar_Syntax_Syntax.U_succ uu____63304
        | FStar_Syntax_Syntax.U_max us ->
            let uu____63308 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____63308
        | uu____63311 -> u2  in
      let uu____63312 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____63312
  
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
                (let uu____63433 = norm_refinement env t12  in
                 match uu____63433 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____63448;
                     FStar_Syntax_Syntax.vars = uu____63449;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____63473 =
                       let uu____63475 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____63477 = FStar_Syntax_Print.tag_of_term tt
                          in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____63475 uu____63477
                        in
                     failwith uu____63473)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____63493 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____63493
          | FStar_Syntax_Syntax.Tm_uinst uu____63494 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____63531 =
                   let uu____63532 = FStar_Syntax_Subst.compress t1'  in
                   uu____63532.FStar_Syntax_Syntax.n  in
                 match uu____63531 with
                 | FStar_Syntax_Syntax.Tm_refine uu____63547 -> aux true t1'
                 | uu____63555 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____63570 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____63601 =
                   let uu____63602 = FStar_Syntax_Subst.compress t1'  in
                   uu____63602.FStar_Syntax_Syntax.n  in
                 match uu____63601 with
                 | FStar_Syntax_Syntax.Tm_refine uu____63617 -> aux true t1'
                 | uu____63625 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____63640 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____63687 =
                   let uu____63688 = FStar_Syntax_Subst.compress t1'  in
                   uu____63688.FStar_Syntax_Syntax.n  in
                 match uu____63687 with
                 | FStar_Syntax_Syntax.Tm_refine uu____63703 -> aux true t1'
                 | uu____63711 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____63726 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____63741 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____63756 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____63771 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____63786 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____63815 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____63848 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____63869 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____63896 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____63924 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____63961 ->
              let uu____63968 =
                let uu____63970 = FStar_Syntax_Print.term_to_string t12  in
                let uu____63972 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____63970 uu____63972
                 in
              failwith uu____63968
          | FStar_Syntax_Syntax.Tm_ascribed uu____63987 ->
              let uu____64014 =
                let uu____64016 = FStar_Syntax_Print.term_to_string t12  in
                let uu____64018 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____64016 uu____64018
                 in
              failwith uu____64014
          | FStar_Syntax_Syntax.Tm_delayed uu____64033 ->
              let uu____64056 =
                let uu____64058 = FStar_Syntax_Print.term_to_string t12  in
                let uu____64060 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____64058 uu____64060
                 in
              failwith uu____64056
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____64075 =
                let uu____64077 = FStar_Syntax_Print.term_to_string t12  in
                let uu____64079 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____64077 uu____64079
                 in
              failwith uu____64075
           in
        let uu____64094 = whnf env t1  in aux false uu____64094
  
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
      let uu____64155 = base_and_refinement env t  in
      FStar_All.pipe_right uu____64155 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____64196 = FStar_Syntax_Syntax.null_bv t  in
    (uu____64196, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____64223 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____64223 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____64283  ->
    match uu____64283 with
    | (t_base,refopt) ->
        let uu____64314 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____64314 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____64356 =
      let uu____64360 =
        let uu____64363 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____64390  ->
                  match uu____64390 with | (uu____64399,uu____64400,x) -> x))
           in
        FStar_List.append wl.attempting uu____64363  in
      FStar_List.map (wl_prob_to_string wl) uu____64360  in
    FStar_All.pipe_right uu____64356 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____64423 .
    ('Auu____64423 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____64435  ->
    match uu____64435 with
    | (uu____64442,c,args) ->
        let uu____64445 = print_ctx_uvar c  in
        let uu____64447 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____64445 uu____64447
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____64457 = FStar_Syntax_Util.head_and_args t  in
    match uu____64457 with
    | (head1,_args) ->
        let uu____64501 =
          let uu____64502 = FStar_Syntax_Subst.compress head1  in
          uu____64502.FStar_Syntax_Syntax.n  in
        (match uu____64501 with
         | FStar_Syntax_Syntax.Tm_uvar uu____64506 -> true
         | uu____64520 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____64528 = FStar_Syntax_Util.head_and_args t  in
    match uu____64528 with
    | (head1,_args) ->
        let uu____64571 =
          let uu____64572 = FStar_Syntax_Subst.compress head1  in
          uu____64572.FStar_Syntax_Syntax.n  in
        (match uu____64571 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____64576) -> u
         | uu____64593 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____64618 = FStar_Syntax_Util.head_and_args t  in
      match uu____64618 with
      | (head1,args) ->
          let uu____64665 =
            let uu____64666 = FStar_Syntax_Subst.compress head1  in
            uu____64666.FStar_Syntax_Syntax.n  in
          (match uu____64665 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____64674)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____64707 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___603_64732  ->
                         match uu___603_64732 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____64737 =
                               let uu____64738 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____64738.FStar_Syntax_Syntax.n  in
                             (match uu____64737 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____64743 -> false)
                         | uu____64745 -> true))
                  in
               (match uu____64707 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____64770 =
                        FStar_List.collect
                          (fun uu___604_64782  ->
                             match uu___604_64782 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____64786 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____64786]
                             | uu____64787 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____64770 FStar_List.rev  in
                    let uu____64810 =
                      let uu____64817 =
                        let uu____64826 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___605_64848  ->
                                  match uu___605_64848 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____64852 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____64852]
                                  | uu____64853 -> []))
                           in
                        FStar_All.pipe_right uu____64826 FStar_List.rev  in
                      let uu____64876 =
                        let uu____64879 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____64879  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____64817 uu____64876
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____64810 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____64915  ->
                                match uu____64915 with
                                | (x,i) ->
                                    let uu____64934 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____64934, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____64965  ->
                                match uu____64965 with
                                | (a,i) ->
                                    let uu____64984 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____64984, i)) args_sol
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
           | uu____65006 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____65028 =
          let uu____65051 =
            let uu____65052 = FStar_Syntax_Subst.compress k  in
            uu____65052.FStar_Syntax_Syntax.n  in
          match uu____65051 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____65134 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____65134)
              else
                (let uu____65169 = FStar_Syntax_Util.abs_formals t  in
                 match uu____65169 with
                 | (ys',t1,uu____65202) ->
                     let uu____65207 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____65207))
          | uu____65246 ->
              let uu____65247 =
                let uu____65252 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____65252)  in
              ((ys, t), uu____65247)
           in
        match uu____65028 with
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
                 let uu____65347 = FStar_Syntax_Util.rename_binders xs ys1
                    in
                 FStar_Syntax_Subst.subst_comp uu____65347 c  in
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
               (let uu____65425 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____65425
                then
                  let uu____65430 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____65432 = print_ctx_uvar uv  in
                  let uu____65434 = FStar_Syntax_Print.term_to_string phi1
                     in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____65430 uu____65432 uu____65434
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____65443 =
                   let uu____65445 = FStar_Util.string_of_int (p_pid prob)
                      in
                   Prims.op_Hat "solve_prob'.sol." uu____65445  in
                 let uu____65448 =
                   let uu____65451 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____65451
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____65443 uu____65448 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____65484 =
               let uu____65485 =
                 let uu____65487 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____65489 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____65487 uu____65489
                  in
               failwith uu____65485  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____65555  ->
                       match uu____65555 with
                       | (a,i) ->
                           let uu____65576 =
                             let uu____65577 = FStar_Syntax_Subst.compress a
                                in
                             uu____65577.FStar_Syntax_Syntax.n  in
                           (match uu____65576 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____65603 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____65613 =
                 let uu____65615 = is_flex g  in
                 Prims.op_Negation uu____65615  in
               if uu____65613
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____65624 = destruct_flex_t g wl  in
                  match uu____65624 with
                  | ((uu____65629,uv1,args),wl1) ->
                      ((let uu____65634 = args_as_binders args  in
                        assign_solution uu____65634 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___1277_65636 = wl1  in
              {
                attempting = (uu___1277_65636.attempting);
                wl_deferred = (uu___1277_65636.wl_deferred);
                ctr = (wl1.ctr + (Prims.parse_int "1"));
                defer_ok = (uu___1277_65636.defer_ok);
                smt_ok = (uu___1277_65636.smt_ok);
                umax_heuristic_ok = (uu___1277_65636.umax_heuristic_ok);
                tcenv = (uu___1277_65636.tcenv);
                wl_implicits = (uu___1277_65636.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____65661 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____65661
         then
           let uu____65666 = FStar_Util.string_of_int pid  in
           let uu____65668 =
             let uu____65670 = FStar_List.map (uvi_to_string wl.tcenv) sol
                in
             FStar_All.pipe_right uu____65670 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____65666
             uu____65668
         else ());
        commit sol;
        (let uu___1285_65684 = wl  in
         {
           attempting = (uu___1285_65684.attempting);
           wl_deferred = (uu___1285_65684.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___1285_65684.defer_ok);
           smt_ok = (uu___1285_65684.smt_ok);
           umax_heuristic_ok = (uu___1285_65684.umax_heuristic_ok);
           tcenv = (uu___1285_65684.tcenv);
           wl_implicits = (uu___1285_65684.wl_implicits)
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
             | (uu____65750,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____65778 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____65778
              in
           (let uu____65784 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____65784
            then
              let uu____65789 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____65793 =
                let uu____65795 =
                  FStar_List.map (uvi_to_string wl.tcenv) uvis  in
                FStar_All.pipe_right uu____65795 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____65789
                uu____65793
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
        let uu____65830 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____65830 FStar_Util.set_elements  in
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
      let uu____65870 = occurs uk t  in
      match uu____65870 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____65909 =
                 let uu____65911 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____65913 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____65911 uu____65913
                  in
               FStar_Pervasives_Native.Some uu____65909)
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
            let uu____66033 = maximal_prefix bs_tail bs'_tail  in
            (match uu____66033 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____66084 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____66141  ->
             match uu____66141 with
             | (x,uu____66153) -> (FStar_Syntax_Syntax.Binding_var x) :: g1)
        g bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____66171 = FStar_List.last bs  in
      match uu____66171 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____66195) ->
          let uu____66206 =
            FStar_Util.prefix_until
              (fun uu___606_66221  ->
                 match uu___606_66221 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____66224 -> false) g
             in
          (match uu____66206 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____66238,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____66275 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____66275 with
        | (pfx,uu____66285) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____66297 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____66297 with
             | (uu____66305,src',wl1) ->
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
                 | uu____66419 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____66420 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____66484  ->
                  fun uu____66485  ->
                    match (uu____66484, uu____66485) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____66588 =
                          let uu____66590 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____66590
                           in
                        if uu____66588
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____66624 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____66624
                           then
                             let uu____66641 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____66641)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____66420 with | (isect,uu____66691) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____66727 'Auu____66728 .
    (FStar_Syntax_Syntax.bv * 'Auu____66727) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____66728) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____66786  ->
              fun uu____66787  ->
                match (uu____66786, uu____66787) with
                | ((a,uu____66806),(b,uu____66808)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____66824 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____66824) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____66855  ->
           match uu____66855 with
           | (y,uu____66862) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____66872 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____66872) Prims.list ->
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
                   let uu____67034 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____67034
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____67067 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____67119 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____67163 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____67184 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___607_67192  ->
    match uu___607_67192 with
    | MisMatch (d1,d2) ->
        let uu____67204 =
          let uu____67206 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____67208 =
            let uu____67210 =
              let uu____67212 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____67212 ")"  in
            Prims.op_Hat ") (" uu____67210  in
          Prims.op_Hat uu____67206 uu____67208  in
        Prims.op_Hat "MisMatch (" uu____67204
    | HeadMatch u ->
        let uu____67219 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____67219
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___608_67228  ->
    match uu___608_67228 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____67245 -> HeadMatch false
  
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
          let uu____67267 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____67267 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____67278 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____67302 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____67312 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____67339 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____67339
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____67340 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____67341 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____67342 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____67355 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____67369 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____67393) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____67399,uu____67400) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____67442) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____67467;
             FStar_Syntax_Syntax.index = uu____67468;
             FStar_Syntax_Syntax.sort = t2;_},uu____67470)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____67478 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____67479 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____67480 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____67495 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____67502 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____67522 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____67522
  
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
           { FStar_Syntax_Syntax.blob = uu____67541;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____67542;
             FStar_Syntax_Syntax.ltyp = uu____67543;
             FStar_Syntax_Syntax.rng = uu____67544;_},uu____67545)
            ->
            let uu____67556 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____67556 t21
        | (uu____67557,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____67558;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____67559;
             FStar_Syntax_Syntax.ltyp = uu____67560;
             FStar_Syntax_Syntax.rng = uu____67561;_})
            ->
            let uu____67572 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____67572
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____67584 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____67584
            then FullMatch
            else
              (let uu____67589 =
                 let uu____67598 =
                   let uu____67601 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____67601  in
                 let uu____67602 =
                   let uu____67605 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____67605  in
                 (uu____67598, uu____67602)  in
               MisMatch uu____67589)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____67611),FStar_Syntax_Syntax.Tm_uinst (g,uu____67613)) ->
            let uu____67622 = head_matches env f g  in
            FStar_All.pipe_right uu____67622 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____67623) -> HeadMatch true
        | (uu____67625,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____67629 = FStar_Const.eq_const c d  in
            if uu____67629
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____67639),FStar_Syntax_Syntax.Tm_uvar (uv',uu____67641)) ->
            let uu____67674 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____67674
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____67684),FStar_Syntax_Syntax.Tm_refine (y,uu____67686)) ->
            let uu____67695 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____67695 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____67697),uu____67698) ->
            let uu____67703 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____67703 head_match
        | (uu____67704,FStar_Syntax_Syntax.Tm_refine (x,uu____67706)) ->
            let uu____67711 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____67711 head_match
        | (FStar_Syntax_Syntax.Tm_type
           uu____67712,FStar_Syntax_Syntax.Tm_type uu____67713) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____67715,FStar_Syntax_Syntax.Tm_arrow uu____67716) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____67747),FStar_Syntax_Syntax.Tm_app
           (head',uu____67749)) ->
            let uu____67798 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____67798 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____67800),uu____67801) ->
            let uu____67826 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____67826 head_match
        | (uu____67827,FStar_Syntax_Syntax.Tm_app (head1,uu____67829)) ->
            let uu____67854 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____67854 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____67855,FStar_Syntax_Syntax.Tm_let
           uu____67856) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____67884,FStar_Syntax_Syntax.Tm_match uu____67885) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____67931,FStar_Syntax_Syntax.Tm_abs
           uu____67932) -> HeadMatch true
        | uu____67970 ->
            let uu____67975 =
              let uu____67984 = delta_depth_of_term env t11  in
              let uu____67987 = delta_depth_of_term env t21  in
              (uu____67984, uu____67987)  in
            MisMatch uu____67975
  
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
            (let uu____68053 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____68053
             then
               let uu____68058 = FStar_Syntax_Print.term_to_string t  in
               let uu____68060 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____68058 uu____68060
             else ());
            (let uu____68065 =
               let uu____68066 = FStar_Syntax_Util.un_uinst head1  in
               uu____68066.FStar_Syntax_Syntax.n  in
             match uu____68065 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____68072 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____68072 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____68086 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____68086
                        then
                          let uu____68091 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____68091
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____68096 ->
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
                      let uu____68113 =
                        let uu____68115 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____68115 = FStar_Syntax_Util.Equal  in
                      if uu____68113
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____68122 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____68122
                          then
                            let uu____68127 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____68129 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n"
                              uu____68127 uu____68129
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____68134 -> FStar_Pervasives_Native.None)
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
            (let uu____68286 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____68286
             then
               let uu____68291 = FStar_Syntax_Print.term_to_string t11  in
               let uu____68293 = FStar_Syntax_Print.term_to_string t21  in
               let uu____68295 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____68291
                 uu____68293 uu____68295
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____68323 =
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
               match uu____68323 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____68371 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____68371 with
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
                  uu____68409),uu____68410)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____68431 =
                      let uu____68440 = maybe_inline t11  in
                      let uu____68443 = maybe_inline t21  in
                      (uu____68440, uu____68443)  in
                    match uu____68431 with
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
                 (uu____68486,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  uu____68487))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____68508 =
                      let uu____68517 = maybe_inline t11  in
                      let uu____68520 = maybe_inline t21  in
                      (uu____68517, uu____68520)  in
                    match uu____68508 with
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
             | MisMatch uu____68575 -> fail1 n_delta r t11 t21
             | uu____68584 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____68599 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____68599
           then
             let uu____68604 = FStar_Syntax_Print.term_to_string t1  in
             let uu____68606 = FStar_Syntax_Print.term_to_string t2  in
             let uu____68608 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____68616 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____68633 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____68633
                    (fun uu____68668  ->
                       match uu____68668 with
                       | (t11,t21) ->
                           let uu____68676 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____68678 =
                             let uu____68680 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____68680  in
                           Prims.op_Hat uu____68676 uu____68678))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____68604 uu____68606 uu____68608 uu____68616
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____68697 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____68697 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___609_68712  ->
    match uu___609_68712 with
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
      let uu___1789_68761 = p  in
      let uu____68764 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____68765 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1789_68761.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____68764;
        FStar_TypeChecker_Common.relation =
          (uu___1789_68761.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____68765;
        FStar_TypeChecker_Common.element =
          (uu___1789_68761.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1789_68761.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1789_68761.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1789_68761.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1789_68761.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1789_68761.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____68780 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____68780
            (fun _68785  -> FStar_TypeChecker_Common.TProb _68785)
      | FStar_TypeChecker_Common.CProb uu____68786 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____68809 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____68809 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____68817 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____68817 with
           | (lh,lhs_args) ->
               let uu____68864 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____68864 with
                | (rh,rhs_args) ->
                    let uu____68911 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____68924,FStar_Syntax_Syntax.Tm_uvar uu____68925)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____69014 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____69041,uu____69042)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____69057,FStar_Syntax_Syntax.Tm_uvar uu____69058)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____69073,FStar_Syntax_Syntax.Tm_arrow
                         uu____69074) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_69104 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_69104.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_69104.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_69104.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_69104.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_69104.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_69104.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_69104.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_69104.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_69104.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____69107,FStar_Syntax_Syntax.Tm_type uu____69108)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_69124 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_69124.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_69124.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_69124.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_69124.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_69124.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_69124.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_69124.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_69124.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_69124.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____69127,FStar_Syntax_Syntax.Tm_uvar uu____69128)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_69144 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_69144.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_69144.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_69144.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_69144.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_69144.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_69144.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_69144.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_69144.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_69144.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____69147,FStar_Syntax_Syntax.Tm_uvar uu____69148)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____69163,uu____69164)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____69179,FStar_Syntax_Syntax.Tm_uvar uu____69180)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____69195,uu____69196) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____68911 with
                     | (rank,tp1) ->
                         let uu____69209 =
                           FStar_All.pipe_right
                             (let uu___1860_69213 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1860_69213.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1860_69213.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1860_69213.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1860_69213.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1860_69213.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1860_69213.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1860_69213.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1860_69213.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1860_69213.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _69216  ->
                                FStar_TypeChecker_Common.TProb _69216)
                            in
                         (rank, uu____69209))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____69220 =
            FStar_All.pipe_right
              (let uu___1864_69224 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1864_69224.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1864_69224.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1864_69224.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1864_69224.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1864_69224.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1864_69224.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1864_69224.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1864_69224.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1864_69224.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _69227  -> FStar_TypeChecker_Common.CProb _69227)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____69220)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____69287 probs =
      match uu____69287 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____69368 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____69389 = rank wl.tcenv hd1  in
               (match uu____69389 with
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
                      (let uu____69450 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____69455 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____69455)
                          in
                       if uu____69450
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
          let uu____69528 = FStar_Syntax_Util.head_and_args t  in
          match uu____69528 with
          | (hd1,uu____69547) ->
              let uu____69572 =
                let uu____69573 = FStar_Syntax_Subst.compress hd1  in
                uu____69573.FStar_Syntax_Syntax.n  in
              (match uu____69572 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____69578) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____69613  ->
                           match uu____69613 with
                           | (y,uu____69622) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____69645  ->
                                       match uu____69645 with
                                       | (x,uu____69654) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____69659 -> false)
           in
        let uu____69661 = rank tcenv p  in
        match uu____69661 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____69670 -> true
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
    match projectee with | UDeferred _0 -> true | uu____69707 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____69726 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____69746 -> false
  
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
                        let uu____69808 = FStar_Syntax_Util.univ_kernel u3
                           in
                        match uu____69808 with
                        | (k,uu____69816) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____69829 -> false)))
            | uu____69831 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____69883 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____69891 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____69891 = (Prims.parse_int "0")))
                           in
                        if uu____69883 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____69912 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____69920 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____69920 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____69912)
               in
            let uu____69924 = filter1 u12  in
            let uu____69927 = filter1 u22  in (uu____69924, uu____69927)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then UFailed "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____69962 = filter_out_common_univs us1 us2  in
                   (match uu____69962 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____70022 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____70022 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____70025 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          (let uu____70036 =
                             let uu____70038 =
                               FStar_Syntax_Print.univ_to_string u12  in
                             let uu____70040 =
                               FStar_Syntax_Print.univ_to_string u22  in
                             FStar_Util.format2
                               "Unable to unify universes: %s and %s"
                               uu____70038 uu____70040
                              in
                           UFailed uu____70036))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____70066 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____70066 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____70092 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____70092 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____70095 ->
                   let uu____70100 =
                     let uu____70102 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____70104 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format3
                       "Unable to unify universes: %s and %s (%s)"
                       uu____70102 uu____70104 msg
                      in
                   UFailed uu____70100)
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____70107,uu____70108) ->
              let uu____70110 =
                let uu____70112 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____70114 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____70112 uu____70114
                 in
              failwith uu____70110
          | (FStar_Syntax_Syntax.U_unknown ,uu____70117) ->
              let uu____70118 =
                let uu____70120 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____70122 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____70120 uu____70122
                 in
              failwith uu____70118
          | (uu____70125,FStar_Syntax_Syntax.U_bvar uu____70126) ->
              let uu____70128 =
                let uu____70130 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____70132 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____70130 uu____70132
                 in
              failwith uu____70128
          | (uu____70135,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____70136 =
                let uu____70138 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____70140 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____70138 uu____70140
                 in
              failwith uu____70136
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____70170 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____70170
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____70187 = occurs_univ v1 u3  in
              if uu____70187
              then
                let uu____70190 =
                  let uu____70192 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____70194 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____70192 uu____70194
                   in
                try_umax_components u11 u21 uu____70190
              else
                (let uu____70199 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____70199)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____70211 = occurs_univ v1 u3  in
              if uu____70211
              then
                let uu____70214 =
                  let uu____70216 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____70218 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____70216 uu____70218
                   in
                try_umax_components u11 u21 uu____70214
              else
                (let uu____70223 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____70223)
          | (FStar_Syntax_Syntax.U_max uu____70224,uu____70225) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____70233 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____70233
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____70239,FStar_Syntax_Syntax.U_max uu____70240) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____70248 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____70248
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____70254,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____70256,FStar_Syntax_Syntax.U_name uu____70257) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____70259) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____70261) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____70263,FStar_Syntax_Syntax.U_succ uu____70264) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____70266,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____70373 = bc1  in
      match uu____70373 with
      | (bs1,mk_cod1) ->
          let uu____70417 = bc2  in
          (match uu____70417 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____70528 = aux xs ys  in
                     (match uu____70528 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____70611 =
                       let uu____70618 = mk_cod1 xs  in ([], uu____70618)  in
                     let uu____70621 =
                       let uu____70628 = mk_cod2 ys  in ([], uu____70628)  in
                     (uu____70611, uu____70621)
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
                  let uu____70697 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____70697 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____70700 =
                    let uu____70701 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____70701 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____70700
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____70706 = has_type_guard t1 t2  in (uu____70706, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____70707 = has_type_guard t2 t1  in (uu____70707, wl)
  
let is_flex_pat :
  'Auu____70717 'Auu____70718 'Auu____70719 .
    ('Auu____70717 * 'Auu____70718 * 'Auu____70719 Prims.list) -> Prims.bool
  =
  fun uu___610_70733  ->
    match uu___610_70733 with
    | (uu____70742,uu____70743,[]) -> true
    | uu____70747 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____70780 = f  in
      match uu____70780 with
      | (uu____70787,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____70788;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____70789;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____70792;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____70793;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____70794;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____70795;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____70865  ->
                 match uu____70865 with
                 | (y,uu____70874) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____71028 =
                  let uu____71043 =
                    let uu____71046 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____71046  in
                  ((FStar_List.rev pat_binders), uu____71043)  in
                FStar_Pervasives_Native.Some uu____71028
            | (uu____71079,[]) ->
                let uu____71110 =
                  let uu____71125 =
                    let uu____71128 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____71128  in
                  ((FStar_List.rev pat_binders), uu____71125)  in
                FStar_Pervasives_Native.Some uu____71110
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____71219 =
                  let uu____71220 = FStar_Syntax_Subst.compress a  in
                  uu____71220.FStar_Syntax_Syntax.n  in
                (match uu____71219 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____71240 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____71240
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___2188_71270 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___2188_71270.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___2188_71270.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____71274 =
                            let uu____71275 =
                              let uu____71282 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____71282)  in
                            FStar_Syntax_Syntax.NT uu____71275  in
                          [uu____71274]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___2194_71298 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2194_71298.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2194_71298.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____71299 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____71339 =
                  let uu____71354 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____71354  in
                (match uu____71339 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____71429 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____71462 ->
               let uu____71463 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____71463 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____71785 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____71785
       then
         let uu____71790 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____71790
       else ());
      (let uu____71795 = next_prob probs  in
       match uu____71795 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___2219_71822 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___2219_71822.wl_deferred);
               ctr = (uu___2219_71822.ctr);
               defer_ok = (uu___2219_71822.defer_ok);
               smt_ok = (uu___2219_71822.smt_ok);
               umax_heuristic_ok = (uu___2219_71822.umax_heuristic_ok);
               tcenv = (uu___2219_71822.tcenv);
               wl_implicits = (uu___2219_71822.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____71831 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____71831
                 then
                   let uu____71834 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____71834
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
                           (let uu___2231_71846 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___2231_71846.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___2231_71846.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___2231_71846.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___2231_71846.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___2231_71846.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___2231_71846.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___2231_71846.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___2231_71846.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___2231_71846.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____71872 ->
                let uu____71883 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____71954  ->
                          match uu____71954 with
                          | (c,uu____71965,uu____71966) -> c < probs.ctr))
                   in
                (match uu____71883 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____72021 =
                            let uu____72026 =
                              FStar_List.map
                                (fun uu____72044  ->
                                   match uu____72044 with
                                   | (uu____72058,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____72026, (probs.wl_implicits))  in
                          Success uu____72021
                      | uu____72066 ->
                          let uu____72077 =
                            let uu___2249_72078 = probs  in
                            let uu____72079 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____72102  ->
                                      match uu____72102 with
                                      | (uu____72111,uu____72112,y) -> y))
                               in
                            {
                              attempting = uu____72079;
                              wl_deferred = rest;
                              ctr = (uu___2249_72078.ctr);
                              defer_ok = (uu___2249_72078.defer_ok);
                              smt_ok = (uu___2249_72078.smt_ok);
                              umax_heuristic_ok =
                                (uu___2249_72078.umax_heuristic_ok);
                              tcenv = (uu___2249_72078.tcenv);
                              wl_implicits = (uu___2249_72078.wl_implicits)
                            }  in
                          solve env uu____72077))))

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
            let uu____72123 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____72123 with
            | USolved wl1 ->
                let uu____72125 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____72125
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
                  let uu____72179 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____72179 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____72182 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____72195;
                  FStar_Syntax_Syntax.vars = uu____72196;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____72199;
                  FStar_Syntax_Syntax.vars = uu____72200;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____72213,uu____72214) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____72222,FStar_Syntax_Syntax.Tm_uinst uu____72223) ->
                failwith "Impossible: expect head symbols to match"
            | uu____72231 -> USolved wl

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
            ((let uu____72243 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____72243
              then
                let uu____72248 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____72248 msg
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
               let uu____72340 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____72340 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____72395 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____72395
                then
                  let uu____72400 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____72402 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____72400 uu____72402
                else ());
               (let uu____72407 = head_matches_delta env1 wl2 t1 t2  in
                match uu____72407 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____72453 = eq_prob t1 t2 wl2  in
                         (match uu____72453 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____72474 ->
                         let uu____72483 = eq_prob t1 t2 wl2  in
                         (match uu____72483 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____72533 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____72548 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____72549 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____72548, uu____72549)
                           | FStar_Pervasives_Native.None  ->
                               let uu____72554 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____72555 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____72554, uu____72555)
                            in
                         (match uu____72533 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____72586 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____72586 with
                                | (t1_hd,t1_args) ->
                                    let uu____72631 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____72631 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____72697 =
                                              let uu____72704 =
                                                let uu____72715 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____72715 :: t1_args  in
                                              let uu____72732 =
                                                let uu____72741 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____72741 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____72790  ->
                                                   fun uu____72791  ->
                                                     fun uu____72792  ->
                                                       match (uu____72790,
                                                               uu____72791,
                                                               uu____72792)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____72842),
                                                          (a2,uu____72844))
                                                           ->
                                                           let uu____72881 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____72881
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____72704
                                                uu____72732
                                               in
                                            match uu____72697 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___2403_72907 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___2403_72907.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___2403_72907.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___2403_72907.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____72919 =
                                                  solve env1 wl'  in
                                                (match uu____72919 with
                                                 | Success (uu____72922,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___2412_72926
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___2412_72926.attempting);
                                                            wl_deferred =
                                                              (uu___2412_72926.wl_deferred);
                                                            ctr =
                                                              (uu___2412_72926.ctr);
                                                            defer_ok =
                                                              (uu___2412_72926.defer_ok);
                                                            smt_ok =
                                                              (uu___2412_72926.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___2412_72926.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___2412_72926.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____72927 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____72960 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____72960 with
                                | (t1_base,p1_opt) ->
                                    let uu____72996 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____72996 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____73095 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____73095
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
                                               let uu____73148 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____73148
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
                                               let uu____73180 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____73180
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
                                               let uu____73212 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____73212
                                           | uu____73215 -> t_base  in
                                         let uu____73232 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____73232 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____73246 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____73246, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____73253 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____73253 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____73289 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____73289 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____73325 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____73325
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
                              let uu____73349 = combine t11 t21 wl2  in
                              (match uu____73349 with
                               | (t12,ps,wl3) ->
                                   ((let uu____73382 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____73382
                                     then
                                       let uu____73387 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____73387
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____73429 ts1 =
               match uu____73429 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____73492 = pairwise out t wl2  in
                        (match uu____73492 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____73528 =
               let uu____73539 = FStar_List.hd ts  in (uu____73539, [], wl1)
                in
             let uu____73548 = FStar_List.tl ts  in
             aux uu____73528 uu____73548  in
           let uu____73555 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____73555 with
           | (this_flex,this_rigid) ->
               let uu____73581 =
                 let uu____73582 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____73582.FStar_Syntax_Syntax.n  in
               (match uu____73581 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____73607 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____73607
                    then
                      let uu____73610 = destruct_flex_t this_flex wl  in
                      (match uu____73610 with
                       | (flex,wl1) ->
                           let uu____73617 = quasi_pattern env flex  in
                           (match uu____73617 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____73636 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____73636
                                  then
                                    let uu____73641 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____73641
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____73648 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2514_73651 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2514_73651.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2514_73651.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2514_73651.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2514_73651.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2514_73651.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2514_73651.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2514_73651.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2514_73651.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2514_73651.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____73648)
                | uu____73652 ->
                    ((let uu____73654 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____73654
                      then
                        let uu____73659 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____73659
                      else ());
                     (let uu____73664 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____73664 with
                      | (u,_args) ->
                          let uu____73707 =
                            let uu____73708 = FStar_Syntax_Subst.compress u
                               in
                            uu____73708.FStar_Syntax_Syntax.n  in
                          (match uu____73707 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____73736 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____73736 with
                                 | (u',uu____73755) ->
                                     let uu____73780 =
                                       let uu____73781 = whnf env u'  in
                                       uu____73781.FStar_Syntax_Syntax.n  in
                                     (match uu____73780 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____73803 -> false)
                                  in
                               let uu____73805 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___611_73828  ->
                                         match uu___611_73828 with
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
                                              | uu____73842 -> false)
                                         | uu____73846 -> false))
                                  in
                               (match uu____73805 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____73861 = whnf env this_rigid
                                         in
                                      let uu____73862 =
                                        FStar_List.collect
                                          (fun uu___612_73868  ->
                                             match uu___612_73868 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____73874 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____73874]
                                             | uu____73878 -> [])
                                          bounds_probs
                                         in
                                      uu____73861 :: uu____73862  in
                                    let uu____73879 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____73879 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____73912 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____73927 =
                                               let uu____73928 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____73928.FStar_Syntax_Syntax.n
                                                in
                                             match uu____73927 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____73940 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____73940)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____73951 -> bound  in
                                           let uu____73952 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____73952)  in
                                         (match uu____73912 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____73987 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____73987
                                                then
                                                  let wl'1 =
                                                    let uu___2574_73993 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2574_73993.wl_deferred);
                                                      ctr =
                                                        (uu___2574_73993.ctr);
                                                      defer_ok =
                                                        (uu___2574_73993.defer_ok);
                                                      smt_ok =
                                                        (uu___2574_73993.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2574_73993.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2574_73993.tcenv);
                                                      wl_implicits =
                                                        (uu___2574_73993.wl_implicits)
                                                    }  in
                                                  let uu____73994 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____73994
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____74000 =
                                                  solve_t env eq_prob
                                                    (let uu___2579_74002 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2579_74002.wl_deferred);
                                                       ctr =
                                                         (uu___2579_74002.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2579_74002.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2579_74002.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2579_74002.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____74000 with
                                                | Success (uu____74004,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2585_74007 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2585_74007.wl_deferred);
                                                        ctr =
                                                          (uu___2585_74007.ctr);
                                                        defer_ok =
                                                          (uu___2585_74007.defer_ok);
                                                        smt_ok =
                                                          (uu___2585_74007.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2585_74007.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2585_74007.tcenv);
                                                        wl_implicits =
                                                          (uu___2585_74007.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2588_74009 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2588_74009.attempting);
                                                        wl_deferred =
                                                          (uu___2588_74009.wl_deferred);
                                                        ctr =
                                                          (uu___2588_74009.ctr);
                                                        defer_ok =
                                                          (uu___2588_74009.defer_ok);
                                                        smt_ok =
                                                          (uu___2588_74009.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2588_74009.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2588_74009.tcenv);
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
                                                    let uu____74025 =
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
                                                    ((let uu____74039 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____74039
                                                      then
                                                        let uu____74044 =
                                                          let uu____74046 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____74046
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____74044
                                                      else ());
                                                     (let uu____74059 =
                                                        let uu____74074 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____74074)
                                                         in
                                                      match uu____74059 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____74096))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____74122 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____74122
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
                                                                  let uu____74142
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____74142))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____74167 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____74167
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
                                                                    let uu____74187
                                                                    =
                                                                    let uu____74192
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____74192
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____74187
                                                                    [] wl2
                                                                     in
                                                                  let uu____74198
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____74198))))
                                                      | uu____74199 ->
                                                          giveup env
                                                            (Prims.op_Hat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____74215 when flip ->
                               let uu____74216 =
                                 let uu____74218 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____74220 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____74218 uu____74220
                                  in
                               failwith uu____74216
                           | uu____74223 ->
                               let uu____74224 =
                                 let uu____74226 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____74228 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____74226 uu____74228
                                  in
                               failwith uu____74224)))))

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
                      (fun uu____74264  ->
                         match uu____74264 with
                         | (x,i) ->
                             let uu____74283 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____74283, i)) bs_lhs
                     in
                  let uu____74286 = lhs  in
                  match uu____74286 with
                  | (uu____74287,u_lhs,uu____74289) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____74386 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____74396 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____74396, univ)
                             in
                          match uu____74386 with
                          | (k,univ) ->
                              let uu____74403 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____74403 with
                               | (uu____74420,u,wl3) ->
                                   let uu____74423 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____74423, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____74449 =
                              let uu____74462 =
                                let uu____74473 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____74473 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____74524  ->
                                   fun uu____74525  ->
                                     match (uu____74524, uu____74525) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____74626 =
                                           let uu____74633 =
                                             let uu____74636 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____74636
                                              in
                                           copy_uvar u_lhs [] uu____74633 wl2
                                            in
                                         (match uu____74626 with
                                          | (uu____74665,t_a,wl3) ->
                                              let uu____74668 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____74668 with
                                               | (uu____74687,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____74462
                                ([], wl1)
                               in
                            (match uu____74449 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2698_74743 = ct  in
                                   let uu____74744 =
                                     let uu____74747 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____74747
                                      in
                                   let uu____74762 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2698_74743.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2698_74743.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____74744;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____74762;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2698_74743.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2701_74780 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2701_74780.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2701_74780.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____74783 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____74783 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____74845 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____74845 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____74856 =
                                          let uu____74861 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____74861)  in
                                        TERM uu____74856  in
                                      let uu____74862 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____74862 with
                                       | (sub_prob,wl3) ->
                                           let uu____74876 =
                                             let uu____74877 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____74877
                                              in
                                           solve env uu____74876))
                             | (x,imp)::formals2 ->
                                 let uu____74899 =
                                   let uu____74906 =
                                     let uu____74909 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____74909
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____74906 wl1
                                    in
                                 (match uu____74899 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____74930 =
                                          let uu____74933 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____74933
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____74930 u_x
                                         in
                                      let uu____74934 =
                                        let uu____74937 =
                                          let uu____74940 =
                                            let uu____74941 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____74941, imp)  in
                                          [uu____74940]  in
                                        FStar_List.append bs_terms
                                          uu____74937
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____74934 formals2 wl2)
                              in
                           let uu____74968 = occurs_check u_lhs arrow1  in
                           (match uu____74968 with
                            | (uu____74981,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____74997 =
                                    let uu____74999 = FStar_Option.get msg
                                       in
                                    Prims.op_Hat "occurs-check failed: "
                                      uu____74999
                                     in
                                  giveup_or_defer env orig wl uu____74997
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
              (let uu____75032 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____75032
               then
                 let uu____75037 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____75040 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____75037 (rel_to_string (p_rel orig)) uu____75040
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____75167 = rhs wl1 scope env1 subst1  in
                     (match uu____75167 with
                      | (rhs_prob,wl2) ->
                          ((let uu____75188 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____75188
                            then
                              let uu____75193 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____75193
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____75271 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____75271 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2770_75273 = hd1  in
                       let uu____75274 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2770_75273.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2770_75273.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____75274
                       }  in
                     let hd21 =
                       let uu___2773_75278 = hd2  in
                       let uu____75279 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2773_75278.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2773_75278.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____75279
                       }  in
                     let uu____75282 =
                       let uu____75287 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____75287
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____75282 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____75308 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____75308
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____75315 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____75315 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____75382 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____75382
                                  in
                               ((let uu____75400 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____75400
                                 then
                                   let uu____75405 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____75407 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____75405
                                     uu____75407
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____75440 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____75476 = aux wl [] env [] bs1 bs2  in
               match uu____75476 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____75531 = attempt sub_probs wl2  in
                   solve env uu____75531)

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
            let uu___2808_75552 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2808_75552.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2808_75552.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____75565 = try_solve env wl'  in
          match uu____75565 with
          | Success (uu____75566,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2817_75570 = wl  in
                  {
                    attempting = (uu___2817_75570.attempting);
                    wl_deferred = (uu___2817_75570.wl_deferred);
                    ctr = (uu___2817_75570.ctr);
                    defer_ok = (uu___2817_75570.defer_ok);
                    smt_ok = (uu___2817_75570.smt_ok);
                    umax_heuristic_ok = (uu___2817_75570.umax_heuristic_ok);
                    tcenv = (uu___2817_75570.tcenv);
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
        (let uu____75582 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____75582 wl)

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
              let uu____75596 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____75596 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____75630 = lhs1  in
              match uu____75630 with
              | (uu____75633,ctx_u,uu____75635) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____75643 ->
                        let uu____75644 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____75644 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____75693 = quasi_pattern env1 lhs1  in
              match uu____75693 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____75727) ->
                  let uu____75732 = lhs1  in
                  (match uu____75732 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____75747 = occurs_check ctx_u rhs1  in
                       (match uu____75747 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____75798 =
                                let uu____75806 =
                                  let uu____75808 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____75808
                                   in
                                FStar_Util.Inl uu____75806  in
                              (uu____75798, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____75836 =
                                 let uu____75838 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____75838  in
                               if uu____75836
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____75865 =
                                    let uu____75873 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____75873  in
                                  let uu____75879 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____75865, uu____75879)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____75923 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____75923 with
              | (rhs_hd,args) ->
                  let uu____75966 = FStar_Util.prefix args  in
                  (match uu____75966 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____76038 = lhs1  in
                       (match uu____76038 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____76042 =
                              let uu____76053 =
                                let uu____76060 =
                                  let uu____76063 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____76063
                                   in
                                copy_uvar u_lhs [] uu____76060 wl1  in
                              match uu____76053 with
                              | (uu____76090,t_last_arg,wl2) ->
                                  let uu____76093 =
                                    let uu____76100 =
                                      let uu____76101 =
                                        let uu____76110 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____76110]  in
                                      FStar_List.append bs_lhs uu____76101
                                       in
                                    copy_uvar u_lhs uu____76100 t_res_lhs wl2
                                     in
                                  (match uu____76093 with
                                   | (uu____76145,lhs',wl3) ->
                                       let uu____76148 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____76148 with
                                        | (uu____76165,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____76042 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____76186 =
                                     let uu____76187 =
                                       let uu____76192 =
                                         let uu____76193 =
                                           let uu____76196 =
                                             let uu____76201 =
                                               let uu____76202 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____76202]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____76201
                                              in
                                           uu____76196
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____76193
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____76192)  in
                                     TERM uu____76187  in
                                   [uu____76186]  in
                                 let uu____76227 =
                                   let uu____76234 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____76234 with
                                   | (p1,wl3) ->
                                       let uu____76254 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____76254 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____76227 with
                                  | (sub_probs,wl3) ->
                                      let uu____76286 =
                                        let uu____76287 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____76287  in
                                      solve env1 uu____76286))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____76321 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____76321 with
                | (uu____76339,args) ->
                    (match args with | [] -> false | uu____76375 -> true)
                 in
              let is_arrow rhs2 =
                let uu____76394 =
                  let uu____76395 = FStar_Syntax_Subst.compress rhs2  in
                  uu____76395.FStar_Syntax_Syntax.n  in
                match uu____76394 with
                | FStar_Syntax_Syntax.Tm_arrow uu____76399 -> true
                | uu____76415 -> false  in
              let uu____76417 = quasi_pattern env1 lhs1  in
              match uu____76417 with
              | FStar_Pervasives_Native.None  ->
                  let uu____76428 =
                    let uu____76430 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                      uu____76430
                     in
                  giveup_or_defer env1 orig1 wl1 uu____76428
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____76439 = is_app rhs1  in
                  if uu____76439
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____76444 = is_arrow rhs1  in
                     if uu____76444
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____76449 =
                          let uu____76451 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heuristic cannot solve %s; rhs not an app or arrow"
                            uu____76451
                           in
                        giveup_or_defer env1 orig1 wl1 uu____76449))
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
                let uu____76462 = lhs  in
                (match uu____76462 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____76466 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____76466 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____76484 =
                              let uu____76488 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____76488
                               in
                            FStar_All.pipe_right uu____76484
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____76509 = occurs_check ctx_uv rhs1  in
                          (match uu____76509 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____76538 =
                                   let uu____76540 = FStar_Option.get msg  in
                                   Prims.op_Hat "occurs-check failed: "
                                     uu____76540
                                    in
                                 giveup_or_defer env orig wl uu____76538
                               else
                                 (let uu____76546 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____76546
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____76553 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____76553
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____76557 =
                                         let uu____76559 =
                                           names_to_string1 fvs2  in
                                         let uu____76561 =
                                           names_to_string1 fvs1  in
                                         let uu____76563 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____76559 uu____76561
                                           uu____76563
                                          in
                                       giveup_or_defer env orig wl
                                         uu____76557)
                                    else first_order orig env wl lhs rhs1))
                      | uu____76575 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____76582 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____76582 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____76608 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____76608
                             | (FStar_Util.Inl msg,uu____76610) ->
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
                  (let uu____76655 =
                     let uu____76672 = quasi_pattern env lhs  in
                     let uu____76679 = quasi_pattern env rhs  in
                     (uu____76672, uu____76679)  in
                   match uu____76655 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____76722 = lhs  in
                       (match uu____76722 with
                        | ({ FStar_Syntax_Syntax.n = uu____76723;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____76725;_},u_lhs,uu____76727)
                            ->
                            let uu____76730 = rhs  in
                            (match uu____76730 with
                             | (uu____76731,u_rhs,uu____76733) ->
                                 let uu____76734 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____76734
                                 then
                                   let uu____76741 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____76741
                                 else
                                   (let uu____76744 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____76744 with
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
                                        let uu____76776 =
                                          let uu____76783 =
                                            let uu____76786 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____76786
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____76783
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____76776 with
                                         | (uu____76798,w,wl1) ->
                                             let w_app =
                                               let uu____76804 =
                                                 let uu____76809 =
                                                   FStar_List.map
                                                     (fun uu____76820  ->
                                                        match uu____76820
                                                        with
                                                        | (z,uu____76828) ->
                                                            let uu____76833 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____76833) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____76809
                                                  in
                                               uu____76804
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____76835 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____76835
                                               then
                                                 let uu____76840 =
                                                   let uu____76844 =
                                                     flex_t_to_string lhs  in
                                                   let uu____76846 =
                                                     let uu____76850 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____76852 =
                                                       let uu____76856 =
                                                         term_to_string w  in
                                                       let uu____76858 =
                                                         let uu____76862 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____76871 =
                                                           let uu____76875 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____76884 =
                                                             let uu____76888
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____76888]
                                                              in
                                                           uu____76875 ::
                                                             uu____76884
                                                            in
                                                         uu____76862 ::
                                                           uu____76871
                                                          in
                                                       uu____76856 ::
                                                         uu____76858
                                                        in
                                                     uu____76850 ::
                                                       uu____76852
                                                      in
                                                   uu____76844 :: uu____76846
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____76840
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____76905 =
                                                     let uu____76910 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____76910)  in
                                                   TERM uu____76905  in
                                                 let uu____76911 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____76911
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____76919 =
                                                        let uu____76924 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____76924)
                                                         in
                                                      TERM uu____76919  in
                                                    [s1; s2])
                                                  in
                                               let uu____76925 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____76925))))))
                   | uu____76926 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____76997 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____76997
            then
              let uu____77002 = FStar_Syntax_Print.term_to_string t1  in
              let uu____77004 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____77006 = FStar_Syntax_Print.term_to_string t2  in
              let uu____77008 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____77002 uu____77004 uu____77006 uu____77008
            else ());
           (let uu____77019 = FStar_Syntax_Util.head_and_args t1  in
            match uu____77019 with
            | (head1,args1) ->
                let uu____77062 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____77062 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____77132 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____77132 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              k false (defer "universe constraints" orig wl3))
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____77158 =
                         let uu____77160 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____77162 = args_to_string args1  in
                         let uu____77166 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____77168 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____77160 uu____77162 uu____77166 uu____77168
                          in
                       giveup env1 uu____77158 orig
                     else
                       (let uu____77175 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____77180 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____77180 = FStar_Syntax_Util.Equal)
                           in
                        if uu____77175
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___3066_77184 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___3066_77184.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___3066_77184.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___3066_77184.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___3066_77184.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___3066_77184.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___3066_77184.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___3066_77184.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___3066_77184.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____77194 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____77194
                                    else solve env1 wl2))
                        else
                          (let uu____77199 = base_and_refinement env1 t1  in
                           match uu____77199 with
                           | (base1,refinement1) ->
                               let uu____77224 = base_and_refinement env1 t2
                                  in
                               (match uu____77224 with
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
                                           let uu____77389 =
                                             FStar_List.fold_right
                                               (fun uu____77429  ->
                                                  fun uu____77430  ->
                                                    match (uu____77429,
                                                            uu____77430)
                                                    with
                                                    | (((a1,uu____77482),
                                                        (a2,uu____77484)),
                                                       (probs,wl3)) ->
                                                        let uu____77533 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____77533
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____77389 with
                                           | (subprobs,wl3) ->
                                               ((let uu____77576 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____77576
                                                 then
                                                   let uu____77581 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____77581
                                                 else ());
                                                (let uu____77587 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____77587
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
                                                    (let uu____77614 =
                                                       mk_sub_probs wl3  in
                                                     match uu____77614 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____77630 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____77630
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____77638 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____77638))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____77662 =
                                                    mk_sub_probs wl3  in
                                                  match uu____77662 with
                                                  | (subprobs,wl4) ->
                                                      let wl5 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          [] wl4
                                                         in
                                                      let uu____77676 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____77676)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____77702 =
                                           match uu____77702 with
                                           | (prob,reason) ->
                                               ((let uu____77713 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____77713
                                                 then
                                                   let uu____77718 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____77720 =
                                                     prob_to_string env2 prob
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____77718 uu____77720
                                                     reason
                                                 else ());
                                                (let uu____77725 =
                                                   let uu____77734 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____77737 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____77734, uu____77737)
                                                    in
                                                 match uu____77725 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____77750 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____77750 with
                                                      | (head1',uu____77768)
                                                          ->
                                                          let uu____77793 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____77793
                                                           with
                                                           | (head2',uu____77811)
                                                               ->
                                                               let uu____77836
                                                                 =
                                                                 let uu____77841
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____77842
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____77841,
                                                                   uu____77842)
                                                                  in
                                                               (match uu____77836
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____77844
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____77844
                                                                    then
                                                                    let uu____77849
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____77851
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____77853
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____77855
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____77849
                                                                    uu____77851
                                                                    uu____77853
                                                                    uu____77855
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____77860
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___3152_77868
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___3152_77868.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___3152_77868.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___3152_77868.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___3152_77868.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___3152_77868.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___3152_77868.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___3152_77868.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___3152_77868.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____77870
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____77870
                                                                    then
                                                                    let uu____77875
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____77875
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____77880 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____77892 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____77892 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____77900 =
                                             let uu____77901 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____77901.FStar_Syntax_Syntax.n
                                              in
                                           match uu____77900 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____77906 -> false  in
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
                                          | uu____77909 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____77912 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___3172_77948 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___3172_77948.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___3172_77948.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___3172_77948.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___3172_77948.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___3172_77948.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___3172_77948.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___3172_77948.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___3172_77948.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____78024 = destruct_flex_t scrutinee wl1  in
             match uu____78024 with
             | ((_t,uv,_args),wl2) ->
                 let uu____78035 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____78035 with
                  | (xs,pat_term,uu____78051,uu____78052) ->
                      let uu____78057 =
                        FStar_List.fold_left
                          (fun uu____78080  ->
                             fun x  ->
                               match uu____78080 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____78101 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____78101 with
                                    | (uu____78120,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____78057 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____78141 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____78141 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___3212_78158 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___3212_78158.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___3212_78158.umax_heuristic_ok);
                                    tcenv = (uu___3212_78158.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____78170 = solve env1 wl'  in
                                (match uu____78170 with
                                 | Success (uu____78173,imps) ->
                                     let wl'1 =
                                       let uu___3220_78176 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___3220_78176.wl_deferred);
                                         ctr = (uu___3220_78176.ctr);
                                         defer_ok =
                                           (uu___3220_78176.defer_ok);
                                         smt_ok = (uu___3220_78176.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___3220_78176.umax_heuristic_ok);
                                         tcenv = (uu___3220_78176.tcenv);
                                         wl_implicits =
                                           (uu___3220_78176.wl_implicits)
                                       }  in
                                     let uu____78177 = solve env1 wl'1  in
                                     (match uu____78177 with
                                      | Success (uu____78180,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___3228_78184 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___3228_78184.attempting);
                                                 wl_deferred =
                                                   (uu___3228_78184.wl_deferred);
                                                 ctr = (uu___3228_78184.ctr);
                                                 defer_ok =
                                                   (uu___3228_78184.defer_ok);
                                                 smt_ok =
                                                   (uu___3228_78184.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3228_78184.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3228_78184.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____78185 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____78192 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____78215 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____78215
                 then
                   let uu____78220 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____78222 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____78220 uu____78222
                 else ());
                (let uu____78227 =
                   let uu____78248 =
                     let uu____78257 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____78257)  in
                   let uu____78264 =
                     let uu____78273 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____78273)  in
                   (uu____78248, uu____78264)  in
                 match uu____78227 with
                 | ((uu____78303,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____78306;
                                   FStar_Syntax_Syntax.vars = uu____78307;_}),
                    (s,t)) ->
                     let uu____78378 =
                       let uu____78380 = is_flex scrutinee  in
                       Prims.op_Negation uu____78380  in
                     if uu____78378
                     then
                       ((let uu____78391 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____78391
                         then
                           let uu____78396 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____78396
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____78415 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____78415
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____78430 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____78430
                           then
                             let uu____78435 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____78437 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____78435 uu____78437
                           else ());
                          (let pat_discriminates uu___613_78462 =
                             match uu___613_78462 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____78478;
                                  FStar_Syntax_Syntax.p = uu____78479;_},FStar_Pervasives_Native.None
                                ,uu____78480) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____78494;
                                  FStar_Syntax_Syntax.p = uu____78495;_},FStar_Pervasives_Native.None
                                ,uu____78496) -> true
                             | uu____78523 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____78626 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____78626 with
                                       | (uu____78628,uu____78629,t') ->
                                           let uu____78647 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____78647 with
                                            | (FullMatch ,uu____78659) ->
                                                true
                                            | (HeadMatch
                                               uu____78673,uu____78674) ->
                                                true
                                            | uu____78689 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____78726 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____78726
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____78737 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____78737 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____78825,uu____78826) ->
                                       branches1
                                   | uu____78971 -> branches  in
                                 let uu____79026 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____79035 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____79035 with
                                        | (p,uu____79039,uu____79040) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _79069  -> FStar_Util.Inr _79069)
                                   uu____79026))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____79099 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____79099 with
                                | (p,uu____79108,e) ->
                                    ((let uu____79127 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____79127
                                      then
                                        let uu____79132 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____79134 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____79132 uu____79134
                                      else ());
                                     (let uu____79139 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _79154  -> FStar_Util.Inr _79154)
                                        uu____79139)))))
                 | ((s,t),(uu____79157,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____79160;
                                         FStar_Syntax_Syntax.vars =
                                           uu____79161;_}))
                     ->
                     let uu____79230 =
                       let uu____79232 = is_flex scrutinee  in
                       Prims.op_Negation uu____79232  in
                     if uu____79230
                     then
                       ((let uu____79243 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____79243
                         then
                           let uu____79248 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____79248
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____79267 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____79267
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____79282 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____79282
                           then
                             let uu____79287 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____79289 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____79287 uu____79289
                           else ());
                          (let pat_discriminates uu___613_79314 =
                             match uu___613_79314 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____79330;
                                  FStar_Syntax_Syntax.p = uu____79331;_},FStar_Pervasives_Native.None
                                ,uu____79332) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____79346;
                                  FStar_Syntax_Syntax.p = uu____79347;_},FStar_Pervasives_Native.None
                                ,uu____79348) -> true
                             | uu____79375 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____79478 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____79478 with
                                       | (uu____79480,uu____79481,t') ->
                                           let uu____79499 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____79499 with
                                            | (FullMatch ,uu____79511) ->
                                                true
                                            | (HeadMatch
                                               uu____79525,uu____79526) ->
                                                true
                                            | uu____79541 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____79578 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____79578
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____79589 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____79589 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____79677,uu____79678) ->
                                       branches1
                                   | uu____79823 -> branches  in
                                 let uu____79878 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____79887 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____79887 with
                                        | (p,uu____79891,uu____79892) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _79921  -> FStar_Util.Inr _79921)
                                   uu____79878))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____79951 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____79951 with
                                | (p,uu____79960,e) ->
                                    ((let uu____79979 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____79979
                                      then
                                        let uu____79984 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____79986 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____79984 uu____79986
                                      else ());
                                     (let uu____79991 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _80006  -> FStar_Util.Inr _80006)
                                        uu____79991)))))
                 | uu____80007 ->
                     ((let uu____80029 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____80029
                       then
                         let uu____80034 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____80036 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____80034 uu____80036
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____80082 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____80082
            then
              let uu____80087 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____80089 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____80091 = FStar_Syntax_Print.term_to_string t1  in
              let uu____80093 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____80087 uu____80089 uu____80091 uu____80093
            else ());
           (let uu____80098 = head_matches_delta env1 wl1 t1 t2  in
            match uu____80098 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____80129,uu____80130) ->
                     let rec may_relate head3 =
                       let uu____80158 =
                         let uu____80159 = FStar_Syntax_Subst.compress head3
                            in
                         uu____80159.FStar_Syntax_Syntax.n  in
                       match uu____80158 with
                       | FStar_Syntax_Syntax.Tm_name uu____80163 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____80165 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____80190 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____80190 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____80192 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____80195
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____80196 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____80199,uu____80200) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____80242) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____80248) ->
                           may_relate t
                       | uu____80253 -> false  in
                     let uu____80255 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____80255 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____80276 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____80276
                          then
                            let uu____80279 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____80279 with
                             | (guard,wl2) ->
                                 let uu____80286 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____80286)
                          else
                            (let uu____80289 =
                               let uu____80291 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____80293 =
                                 let uu____80295 =
                                   let uu____80299 =
                                     delta_depth_of_term env1 head1  in
                                   FStar_Util.bind_opt uu____80299
                                     (fun x  ->
                                        let uu____80306 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____80306)
                                    in
                                 FStar_Util.dflt "" uu____80295  in
                               let uu____80311 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               let uu____80313 =
                                 let uu____80315 =
                                   let uu____80319 =
                                     delta_depth_of_term env1 head2  in
                                   FStar_Util.bind_opt uu____80319
                                     (fun x  ->
                                        let uu____80326 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____80326)
                                    in
                                 FStar_Util.dflt "" uu____80315  in
                               FStar_Util.format4
                                 "head mismatch (%s (%s) vs %s (%s))"
                                 uu____80291 uu____80293 uu____80311
                                 uu____80313
                                in
                             giveup env1 uu____80289 orig))
                 | (HeadMatch (true ),uu____80332) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____80347 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____80347 with
                        | (guard,wl2) ->
                            let uu____80354 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____80354)
                     else
                       (let uu____80357 =
                          let uu____80359 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____80361 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____80359 uu____80361
                           in
                        giveup env1 uu____80357 orig)
                 | (uu____80364,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___3401_80378 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___3401_80378.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___3401_80378.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___3401_80378.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___3401_80378.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___3401_80378.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___3401_80378.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___3401_80378.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___3401_80378.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____80405 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____80405
          then
            let uu____80408 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____80408
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____80414 =
                let uu____80417 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____80417  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____80414 t1);
             (let uu____80436 =
                let uu____80439 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____80439  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____80436 t2);
             (let uu____80458 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____80458
              then
                let uu____80462 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____80464 =
                  let uu____80466 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____80468 =
                    let uu____80470 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____80470  in
                  Prims.op_Hat uu____80466 uu____80468  in
                let uu____80473 =
                  let uu____80475 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____80477 =
                    let uu____80479 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____80479  in
                  Prims.op_Hat uu____80475 uu____80477  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____80462 uu____80464 uu____80473
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____80486,uu____80487) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____80511,FStar_Syntax_Syntax.Tm_delayed uu____80512) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____80536,uu____80537) ->
                  let uu____80564 =
                    let uu___3432_80565 = problem  in
                    let uu____80566 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3432_80565.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____80566;
                      FStar_TypeChecker_Common.relation =
                        (uu___3432_80565.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3432_80565.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3432_80565.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3432_80565.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3432_80565.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3432_80565.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3432_80565.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3432_80565.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____80564 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____80567,uu____80568) ->
                  let uu____80575 =
                    let uu___3438_80576 = problem  in
                    let uu____80577 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3438_80576.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____80577;
                      FStar_TypeChecker_Common.relation =
                        (uu___3438_80576.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3438_80576.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3438_80576.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3438_80576.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3438_80576.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3438_80576.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3438_80576.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3438_80576.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____80575 wl
              | (uu____80578,FStar_Syntax_Syntax.Tm_ascribed uu____80579) ->
                  let uu____80606 =
                    let uu___3444_80607 = problem  in
                    let uu____80608 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3444_80607.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3444_80607.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3444_80607.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____80608;
                      FStar_TypeChecker_Common.element =
                        (uu___3444_80607.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3444_80607.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3444_80607.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3444_80607.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3444_80607.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3444_80607.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____80606 wl
              | (uu____80609,FStar_Syntax_Syntax.Tm_meta uu____80610) ->
                  let uu____80617 =
                    let uu___3450_80618 = problem  in
                    let uu____80619 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3450_80618.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3450_80618.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3450_80618.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____80619;
                      FStar_TypeChecker_Common.element =
                        (uu___3450_80618.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3450_80618.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3450_80618.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3450_80618.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3450_80618.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3450_80618.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____80617 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____80621),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____80623)) ->
                  let uu____80632 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____80632
              | (FStar_Syntax_Syntax.Tm_bvar uu____80633,uu____80634) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____80636,FStar_Syntax_Syntax.Tm_bvar uu____80637) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___614_80707 =
                    match uu___614_80707 with
                    | [] -> c
                    | bs ->
                        let uu____80735 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____80735
                     in
                  let uu____80746 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____80746 with
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
                                    let uu____80895 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____80895
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
                  let mk_t t l uu___615_80984 =
                    match uu___615_80984 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____81026 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____81026 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____81171 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____81172 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____81171
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____81172 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____81174,uu____81175) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____81206 -> true
                    | uu____81226 -> false  in
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
                      (let uu____81286 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3552_81294 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3552_81294.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3552_81294.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3552_81294.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3552_81294.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3552_81294.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3552_81294.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3552_81294.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3552_81294.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3552_81294.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___3552_81294.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3552_81294.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3552_81294.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3552_81294.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3552_81294.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3552_81294.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3552_81294.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3552_81294.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3552_81294.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3552_81294.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3552_81294.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3552_81294.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3552_81294.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3552_81294.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3552_81294.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3552_81294.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3552_81294.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3552_81294.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3552_81294.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3552_81294.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3552_81294.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3552_81294.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3552_81294.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3552_81294.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3552_81294.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3552_81294.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3552_81294.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3552_81294.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3552_81294.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3552_81294.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3552_81294.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____81286 with
                       | (uu____81299,ty,uu____81301) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____81310 =
                                 let uu____81311 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____81311.FStar_Syntax_Syntax.n  in
                               match uu____81310 with
                               | FStar_Syntax_Syntax.Tm_refine uu____81314 ->
                                   let uu____81321 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____81321
                               | uu____81322 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____81325 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____81325
                             then
                               let uu____81330 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____81332 =
                                 let uu____81334 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____81334
                                  in
                               let uu____81335 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____81330 uu____81332 uu____81335
                             else ());
                            r1))
                     in
                  let uu____81340 =
                    let uu____81357 = maybe_eta t1  in
                    let uu____81364 = maybe_eta t2  in
                    (uu____81357, uu____81364)  in
                  (match uu____81340 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3573_81406 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3573_81406.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3573_81406.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3573_81406.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3573_81406.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3573_81406.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3573_81406.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3573_81406.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3573_81406.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____81427 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____81427
                       then
                         let uu____81430 = destruct_flex_t not_abs wl  in
                         (match uu____81430 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_81447 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_81447.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_81447.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_81447.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_81447.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_81447.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_81447.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_81447.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_81447.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____81471 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____81471
                       then
                         let uu____81474 = destruct_flex_t not_abs wl  in
                         (match uu____81474 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_81491 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_81491.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_81491.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_81491.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_81491.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_81491.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_81491.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_81491.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_81491.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____81495 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____81513,FStar_Syntax_Syntax.Tm_abs uu____81514) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____81545 -> true
                    | uu____81565 -> false  in
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
                      (let uu____81625 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3552_81633 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3552_81633.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3552_81633.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3552_81633.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3552_81633.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3552_81633.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3552_81633.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3552_81633.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3552_81633.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3552_81633.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___3552_81633.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3552_81633.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3552_81633.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3552_81633.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3552_81633.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3552_81633.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3552_81633.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3552_81633.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3552_81633.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3552_81633.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3552_81633.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3552_81633.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3552_81633.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3552_81633.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3552_81633.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3552_81633.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3552_81633.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3552_81633.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3552_81633.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3552_81633.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3552_81633.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3552_81633.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3552_81633.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3552_81633.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3552_81633.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3552_81633.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3552_81633.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3552_81633.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3552_81633.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3552_81633.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3552_81633.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____81625 with
                       | (uu____81638,ty,uu____81640) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____81649 =
                                 let uu____81650 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____81650.FStar_Syntax_Syntax.n  in
                               match uu____81649 with
                               | FStar_Syntax_Syntax.Tm_refine uu____81653 ->
                                   let uu____81660 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____81660
                               | uu____81661 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____81664 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____81664
                             then
                               let uu____81669 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____81671 =
                                 let uu____81673 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____81673
                                  in
                               let uu____81674 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____81669 uu____81671 uu____81674
                             else ());
                            r1))
                     in
                  let uu____81679 =
                    let uu____81696 = maybe_eta t1  in
                    let uu____81703 = maybe_eta t2  in
                    (uu____81696, uu____81703)  in
                  (match uu____81679 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3573_81745 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3573_81745.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3573_81745.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3573_81745.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3573_81745.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3573_81745.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3573_81745.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3573_81745.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3573_81745.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____81766 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____81766
                       then
                         let uu____81769 = destruct_flex_t not_abs wl  in
                         (match uu____81769 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_81786 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_81786.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_81786.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_81786.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_81786.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_81786.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_81786.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_81786.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_81786.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____81810 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____81810
                       then
                         let uu____81813 = destruct_flex_t not_abs wl  in
                         (match uu____81813 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_81830 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_81830.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_81830.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_81830.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_81830.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_81830.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_81830.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_81830.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_81830.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____81834 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____81864 =
                    let uu____81869 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____81869 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3613_81897 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3613_81897.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3613_81897.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3615_81899 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3615_81899.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3615_81899.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____81900,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3613_81915 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3613_81915.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3613_81915.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3615_81917 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3615_81917.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3615_81917.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____81918 -> (x1, x2)  in
                  (match uu____81864 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____81937 = as_refinement false env t11  in
                       (match uu____81937 with
                        | (x12,phi11) ->
                            let uu____81945 = as_refinement false env t21  in
                            (match uu____81945 with
                             | (x22,phi21) ->
                                 ((let uu____81954 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____81954
                                   then
                                     ((let uu____81959 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____81961 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____81963 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____81959
                                         uu____81961 uu____81963);
                                      (let uu____81966 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____81968 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____81970 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____81966
                                         uu____81968 uu____81970))
                                   else ());
                                  (let uu____81975 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____81975 with
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
                                         let uu____82046 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____82046
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____82058 =
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
                                         (let uu____82071 =
                                            let uu____82074 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____82074
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____82071
                                            (p_guard base_prob));
                                         (let uu____82093 =
                                            let uu____82096 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____82096
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____82093
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____82115 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____82115)
                                          in
                                       let has_uvars =
                                         (let uu____82120 =
                                            let uu____82122 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____82122
                                             in
                                          Prims.op_Negation uu____82120) ||
                                           (let uu____82126 =
                                              let uu____82128 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____82128
                                               in
                                            Prims.op_Negation uu____82126)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____82132 =
                                           let uu____82137 =
                                             let uu____82146 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____82146]  in
                                           mk_t_problem wl1 uu____82137 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____82132 with
                                          | (ref_prob,wl2) ->
                                              let uu____82168 =
                                                solve env1
                                                  (let uu___3657_82170 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3657_82170.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3657_82170.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3657_82170.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3657_82170.tcenv);
                                                     wl_implicits =
                                                       (uu___3657_82170.wl_implicits)
                                                   })
                                                 in
                                              (match uu____82168 with
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
                                               | Success uu____82187 ->
                                                   let guard =
                                                     let uu____82195 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____82195
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___3668_82204 =
                                                       wl3  in
                                                     {
                                                       attempting =
                                                         (uu___3668_82204.attempting);
                                                       wl_deferred =
                                                         (uu___3668_82204.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            (Prims.parse_int "1"));
                                                       defer_ok =
                                                         (uu___3668_82204.defer_ok);
                                                       smt_ok =
                                                         (uu___3668_82204.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___3668_82204.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___3668_82204.tcenv);
                                                       wl_implicits =
                                                         (uu___3668_82204.wl_implicits)
                                                     }  in
                                                   let uu____82206 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____82206))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____82209,FStar_Syntax_Syntax.Tm_uvar uu____82210) ->
                  let uu____82235 = destruct_flex_t t1 wl  in
                  (match uu____82235 with
                   | (f1,wl1) ->
                       let uu____82242 = destruct_flex_t t2 wl1  in
                       (match uu____82242 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82249;
                    FStar_Syntax_Syntax.pos = uu____82250;
                    FStar_Syntax_Syntax.vars = uu____82251;_},uu____82252),FStar_Syntax_Syntax.Tm_uvar
                 uu____82253) ->
                  let uu____82302 = destruct_flex_t t1 wl  in
                  (match uu____82302 with
                   | (f1,wl1) ->
                       let uu____82309 = destruct_flex_t t2 wl1  in
                       (match uu____82309 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____82316,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82317;
                    FStar_Syntax_Syntax.pos = uu____82318;
                    FStar_Syntax_Syntax.vars = uu____82319;_},uu____82320))
                  ->
                  let uu____82369 = destruct_flex_t t1 wl  in
                  (match uu____82369 with
                   | (f1,wl1) ->
                       let uu____82376 = destruct_flex_t t2 wl1  in
                       (match uu____82376 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82383;
                    FStar_Syntax_Syntax.pos = uu____82384;
                    FStar_Syntax_Syntax.vars = uu____82385;_},uu____82386),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82387;
                    FStar_Syntax_Syntax.pos = uu____82388;
                    FStar_Syntax_Syntax.vars = uu____82389;_},uu____82390))
                  ->
                  let uu____82463 = destruct_flex_t t1 wl  in
                  (match uu____82463 with
                   | (f1,wl1) ->
                       let uu____82470 = destruct_flex_t t2 wl1  in
                       (match uu____82470 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____82477,uu____82478) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____82491 = destruct_flex_t t1 wl  in
                  (match uu____82491 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82498;
                    FStar_Syntax_Syntax.pos = uu____82499;
                    FStar_Syntax_Syntax.vars = uu____82500;_},uu____82501),uu____82502)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____82539 = destruct_flex_t t1 wl  in
                  (match uu____82539 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____82546,FStar_Syntax_Syntax.Tm_uvar uu____82547) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____82560,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82561;
                    FStar_Syntax_Syntax.pos = uu____82562;
                    FStar_Syntax_Syntax.vars = uu____82563;_},uu____82564))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____82601,FStar_Syntax_Syntax.Tm_arrow uu____82602) ->
                  solve_t' env
                    (let uu___3768_82630 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3768_82630.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3768_82630.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3768_82630.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3768_82630.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3768_82630.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3768_82630.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3768_82630.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3768_82630.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3768_82630.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82631;
                    FStar_Syntax_Syntax.pos = uu____82632;
                    FStar_Syntax_Syntax.vars = uu____82633;_},uu____82634),FStar_Syntax_Syntax.Tm_arrow
                 uu____82635) ->
                  solve_t' env
                    (let uu___3768_82687 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3768_82687.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3768_82687.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3768_82687.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3768_82687.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3768_82687.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3768_82687.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3768_82687.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3768_82687.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3768_82687.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____82688,FStar_Syntax_Syntax.Tm_uvar uu____82689) ->
                  let uu____82702 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____82702
              | (uu____82703,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82704;
                    FStar_Syntax_Syntax.pos = uu____82705;
                    FStar_Syntax_Syntax.vars = uu____82706;_},uu____82707))
                  ->
                  let uu____82744 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____82744
              | (FStar_Syntax_Syntax.Tm_uvar uu____82745,uu____82746) ->
                  let uu____82759 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____82759
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82760;
                    FStar_Syntax_Syntax.pos = uu____82761;
                    FStar_Syntax_Syntax.vars = uu____82762;_},uu____82763),uu____82764)
                  ->
                  let uu____82801 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____82801
              | (FStar_Syntax_Syntax.Tm_refine uu____82802,uu____82803) ->
                  let t21 =
                    let uu____82811 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____82811  in
                  solve_t env
                    (let uu___3803_82837 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3803_82837.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3803_82837.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3803_82837.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3803_82837.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3803_82837.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3803_82837.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3803_82837.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3803_82837.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3803_82837.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____82838,FStar_Syntax_Syntax.Tm_refine uu____82839) ->
                  let t11 =
                    let uu____82847 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____82847  in
                  solve_t env
                    (let uu___3810_82873 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3810_82873.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3810_82873.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3810_82873.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3810_82873.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3810_82873.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3810_82873.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3810_82873.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3810_82873.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3810_82873.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____82955 =
                    let uu____82956 = guard_of_prob env wl problem t1 t2  in
                    match uu____82956 with
                    | (guard,wl1) ->
                        let uu____82963 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____82963
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____83182 = br1  in
                        (match uu____83182 with
                         | (p1,w1,uu____83211) ->
                             let uu____83228 = br2  in
                             (match uu____83228 with
                              | (p2,w2,uu____83251) ->
                                  let uu____83256 =
                                    let uu____83258 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____83258  in
                                  if uu____83256
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____83285 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____83285 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____83322 = br2  in
                                         (match uu____83322 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____83355 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____83355
                                                 in
                                              let uu____83360 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____83391,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____83412) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____83471 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____83471 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____83360
                                                (fun uu____83543  ->
                                                   match uu____83543 with
                                                   | (wprobs,wl2) ->
                                                       let uu____83580 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____83580
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____83601
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____83601
                                                              then
                                                                let uu____83606
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____83608
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____83606
                                                                  uu____83608
                                                              else ());
                                                             (let uu____83614
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____83614
                                                                (fun
                                                                   uu____83650
                                                                    ->
                                                                   match uu____83650
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
                    | uu____83779 -> FStar_Pervasives_Native.None  in
                  let uu____83820 = solve_branches wl brs1 brs2  in
                  (match uu____83820 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____83871 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____83871 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____83905 =
                                FStar_List.map
                                  (fun uu____83917  ->
                                     match uu____83917 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____83905  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____83926 =
                              let uu____83927 =
                                let uu____83928 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____83928
                                  (let uu___3909_83936 = wl3  in
                                   {
                                     attempting =
                                       (uu___3909_83936.attempting);
                                     wl_deferred =
                                       (uu___3909_83936.wl_deferred);
                                     ctr = (uu___3909_83936.ctr);
                                     defer_ok = (uu___3909_83936.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3909_83936.umax_heuristic_ok);
                                     tcenv = (uu___3909_83936.tcenv);
                                     wl_implicits =
                                       (uu___3909_83936.wl_implicits)
                                   })
                                 in
                              solve env uu____83927  in
                            (match uu____83926 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____83941 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____83948,uu____83949) ->
                  let head1 =
                    let uu____83973 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____83973
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84019 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84019
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____84065 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____84065
                    then
                      let uu____84069 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____84071 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____84073 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____84069 uu____84071 uu____84073
                    else ());
                   (let no_free_uvars t =
                      (let uu____84087 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____84087) &&
                        (let uu____84091 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____84091)
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
                      let uu____84108 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____84108 = FStar_Syntax_Util.Equal  in
                    let uu____84109 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____84109
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____84113 = equal t1 t2  in
                         (if uu____84113
                          then
                            let uu____84116 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____84116
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____84121 =
                            let uu____84128 = equal t1 t2  in
                            if uu____84128
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____84141 = mk_eq2 wl env orig t1 t2  in
                               match uu____84141 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____84121 with
                          | (guard,wl1) ->
                              let uu____84162 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____84162))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____84165,uu____84166) ->
                  let head1 =
                    let uu____84174 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84174
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84220 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84220
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____84266 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____84266
                    then
                      let uu____84270 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____84272 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____84274 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____84270 uu____84272 uu____84274
                    else ());
                   (let no_free_uvars t =
                      (let uu____84288 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____84288) &&
                        (let uu____84292 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____84292)
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
                      let uu____84309 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____84309 = FStar_Syntax_Util.Equal  in
                    let uu____84310 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____84310
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____84314 = equal t1 t2  in
                         (if uu____84314
                          then
                            let uu____84317 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____84317
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____84322 =
                            let uu____84329 = equal t1 t2  in
                            if uu____84329
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____84342 = mk_eq2 wl env orig t1 t2  in
                               match uu____84342 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____84322 with
                          | (guard,wl1) ->
                              let uu____84363 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____84363))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____84366,uu____84367) ->
                  let head1 =
                    let uu____84369 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84369
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84415 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84415
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____84461 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____84461
                    then
                      let uu____84465 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____84467 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____84469 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____84465 uu____84467 uu____84469
                    else ());
                   (let no_free_uvars t =
                      (let uu____84483 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____84483) &&
                        (let uu____84487 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____84487)
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
                      let uu____84504 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____84504 = FStar_Syntax_Util.Equal  in
                    let uu____84505 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____84505
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____84509 = equal t1 t2  in
                         (if uu____84509
                          then
                            let uu____84512 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____84512
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____84517 =
                            let uu____84524 = equal t1 t2  in
                            if uu____84524
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____84537 = mk_eq2 wl env orig t1 t2  in
                               match uu____84537 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____84517 with
                          | (guard,wl1) ->
                              let uu____84558 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____84558))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____84561,uu____84562) ->
                  let head1 =
                    let uu____84564 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84564
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84610 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84610
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____84656 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____84656
                    then
                      let uu____84660 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____84662 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____84664 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____84660 uu____84662 uu____84664
                    else ());
                   (let no_free_uvars t =
                      (let uu____84678 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____84678) &&
                        (let uu____84682 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____84682)
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
                      let uu____84699 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____84699 = FStar_Syntax_Util.Equal  in
                    let uu____84700 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____84700
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____84704 = equal t1 t2  in
                         (if uu____84704
                          then
                            let uu____84707 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____84707
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____84712 =
                            let uu____84719 = equal t1 t2  in
                            if uu____84719
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____84732 = mk_eq2 wl env orig t1 t2  in
                               match uu____84732 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____84712 with
                          | (guard,wl1) ->
                              let uu____84753 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____84753))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____84756,uu____84757) ->
                  let head1 =
                    let uu____84759 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84759
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84805 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84805
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____84851 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____84851
                    then
                      let uu____84855 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____84857 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____84859 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____84855 uu____84857 uu____84859
                    else ());
                   (let no_free_uvars t =
                      (let uu____84873 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____84873) &&
                        (let uu____84877 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____84877)
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
                      let uu____84894 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____84894 = FStar_Syntax_Util.Equal  in
                    let uu____84895 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____84895
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____84899 = equal t1 t2  in
                         (if uu____84899
                          then
                            let uu____84902 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____84902
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____84907 =
                            let uu____84914 = equal t1 t2  in
                            if uu____84914
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____84927 = mk_eq2 wl env orig t1 t2  in
                               match uu____84927 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____84907 with
                          | (guard,wl1) ->
                              let uu____84948 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____84948))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____84951,uu____84952) ->
                  let head1 =
                    let uu____84970 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84970
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85016 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85016
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85062 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85062
                    then
                      let uu____85066 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85068 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85070 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85066 uu____85068 uu____85070
                    else ());
                   (let no_free_uvars t =
                      (let uu____85084 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85084) &&
                        (let uu____85088 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85088)
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
                      let uu____85105 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85105 = FStar_Syntax_Util.Equal  in
                    let uu____85106 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85106
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85110 = equal t1 t2  in
                         (if uu____85110
                          then
                            let uu____85113 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85113
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85118 =
                            let uu____85125 = equal t1 t2  in
                            if uu____85125
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85138 = mk_eq2 wl env orig t1 t2  in
                               match uu____85138 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85118 with
                          | (guard,wl1) ->
                              let uu____85159 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85159))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____85162,FStar_Syntax_Syntax.Tm_match uu____85163) ->
                  let head1 =
                    let uu____85187 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85187
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85233 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85233
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85279 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85279
                    then
                      let uu____85283 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85285 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85287 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85283 uu____85285 uu____85287
                    else ());
                   (let no_free_uvars t =
                      (let uu____85301 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85301) &&
                        (let uu____85305 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85305)
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
                      let uu____85322 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85322 = FStar_Syntax_Util.Equal  in
                    let uu____85323 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85323
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85327 = equal t1 t2  in
                         (if uu____85327
                          then
                            let uu____85330 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85330
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85335 =
                            let uu____85342 = equal t1 t2  in
                            if uu____85342
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85355 = mk_eq2 wl env orig t1 t2  in
                               match uu____85355 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85335 with
                          | (guard,wl1) ->
                              let uu____85376 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85376))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____85379,FStar_Syntax_Syntax.Tm_uinst uu____85380) ->
                  let head1 =
                    let uu____85388 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85388
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85428 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85428
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85468 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85468
                    then
                      let uu____85472 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85474 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85476 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85472 uu____85474 uu____85476
                    else ());
                   (let no_free_uvars t =
                      (let uu____85490 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85490) &&
                        (let uu____85494 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85494)
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
                      let uu____85511 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85511 = FStar_Syntax_Util.Equal  in
                    let uu____85512 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85512
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85516 = equal t1 t2  in
                         (if uu____85516
                          then
                            let uu____85519 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85519
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85524 =
                            let uu____85531 = equal t1 t2  in
                            if uu____85531
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85544 = mk_eq2 wl env orig t1 t2  in
                               match uu____85544 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85524 with
                          | (guard,wl1) ->
                              let uu____85565 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85565))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____85568,FStar_Syntax_Syntax.Tm_name uu____85569) ->
                  let head1 =
                    let uu____85571 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85571
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85611 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85611
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85651 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85651
                    then
                      let uu____85655 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85657 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85659 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85655 uu____85657 uu____85659
                    else ());
                   (let no_free_uvars t =
                      (let uu____85673 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85673) &&
                        (let uu____85677 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85677)
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
                      let uu____85694 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85694 = FStar_Syntax_Util.Equal  in
                    let uu____85695 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85695
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85699 = equal t1 t2  in
                         (if uu____85699
                          then
                            let uu____85702 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85702
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85707 =
                            let uu____85714 = equal t1 t2  in
                            if uu____85714
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85727 = mk_eq2 wl env orig t1 t2  in
                               match uu____85727 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85707 with
                          | (guard,wl1) ->
                              let uu____85748 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85748))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____85751,FStar_Syntax_Syntax.Tm_constant uu____85752) ->
                  let head1 =
                    let uu____85754 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85754
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85794 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85794
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85834 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85834
                    then
                      let uu____85838 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85840 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85842 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85838 uu____85840 uu____85842
                    else ());
                   (let no_free_uvars t =
                      (let uu____85856 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85856) &&
                        (let uu____85860 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85860)
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
                      let uu____85877 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85877 = FStar_Syntax_Util.Equal  in
                    let uu____85878 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85878
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85882 = equal t1 t2  in
                         (if uu____85882
                          then
                            let uu____85885 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85885
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85890 =
                            let uu____85897 = equal t1 t2  in
                            if uu____85897
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85910 = mk_eq2 wl env orig t1 t2  in
                               match uu____85910 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85890 with
                          | (guard,wl1) ->
                              let uu____85931 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85931))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____85934,FStar_Syntax_Syntax.Tm_fvar uu____85935) ->
                  let head1 =
                    let uu____85937 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85937
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85977 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85977
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____86017 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____86017
                    then
                      let uu____86021 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____86023 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____86025 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____86021 uu____86023 uu____86025
                    else ());
                   (let no_free_uvars t =
                      (let uu____86039 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____86039) &&
                        (let uu____86043 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____86043)
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
                      let uu____86060 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____86060 = FStar_Syntax_Util.Equal  in
                    let uu____86061 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____86061
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____86065 = equal t1 t2  in
                         (if uu____86065
                          then
                            let uu____86068 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____86068
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____86073 =
                            let uu____86080 = equal t1 t2  in
                            if uu____86080
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____86093 = mk_eq2 wl env orig t1 t2  in
                               match uu____86093 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____86073 with
                          | (guard,wl1) ->
                              let uu____86114 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____86114))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____86117,FStar_Syntax_Syntax.Tm_app uu____86118) ->
                  let head1 =
                    let uu____86136 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____86136
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____86176 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____86176
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____86216 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____86216
                    then
                      let uu____86220 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____86222 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____86224 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____86220 uu____86222 uu____86224
                    else ());
                   (let no_free_uvars t =
                      (let uu____86238 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____86238) &&
                        (let uu____86242 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____86242)
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
                      let uu____86259 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____86259 = FStar_Syntax_Util.Equal  in
                    let uu____86260 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____86260
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____86264 = equal t1 t2  in
                         (if uu____86264
                          then
                            let uu____86267 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____86267
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____86272 =
                            let uu____86279 = equal t1 t2  in
                            if uu____86279
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____86292 = mk_eq2 wl env orig t1 t2  in
                               match uu____86292 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____86272 with
                          | (guard,wl1) ->
                              let uu____86313 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____86313))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____86316,FStar_Syntax_Syntax.Tm_let uu____86317) ->
                  let uu____86344 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____86344
                  then
                    let uu____86347 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____86347
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____86351,uu____86352) ->
                  let uu____86366 =
                    let uu____86372 =
                      let uu____86374 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____86376 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____86378 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____86380 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____86374 uu____86376 uu____86378 uu____86380
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____86372)
                     in
                  FStar_Errors.raise_error uu____86366
                    t1.FStar_Syntax_Syntax.pos
              | (uu____86384,FStar_Syntax_Syntax.Tm_let uu____86385) ->
                  let uu____86399 =
                    let uu____86405 =
                      let uu____86407 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____86409 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____86411 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____86413 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____86407 uu____86409 uu____86411 uu____86413
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____86405)
                     in
                  FStar_Errors.raise_error uu____86399
                    t1.FStar_Syntax_Syntax.pos
              | uu____86417 -> giveup env "head tag mismatch" orig))))

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
          (let uu____86481 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____86481
           then
             let uu____86486 =
               let uu____86488 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____86488  in
             let uu____86489 =
               let uu____86491 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____86491  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____86486 uu____86489
           else ());
          (let uu____86495 =
             let uu____86497 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____86497  in
           if uu____86495
           then
             let uu____86500 =
               let uu____86502 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____86504 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____86502 uu____86504
                in
             giveup env uu____86500 orig
           else
             (let uu____86509 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____86509 with
              | (ret_sub_prob,wl1) ->
                  let uu____86517 =
                    FStar_List.fold_right2
                      (fun uu____86554  ->
                         fun uu____86555  ->
                           fun uu____86556  ->
                             match (uu____86554, uu____86555, uu____86556)
                             with
                             | ((a1,uu____86600),(a2,uu____86602),(arg_sub_probs,wl2))
                                 ->
                                 let uu____86635 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____86635 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____86517 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____86665 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____86665  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____86673 = attempt sub_probs wl3  in
                       solve env uu____86673)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____86696 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____86699)::[] -> wp1
              | uu____86724 ->
                  let uu____86735 =
                    let uu____86737 =
                      let uu____86739 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____86739  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____86737
                     in
                  failwith uu____86735
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____86746 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____86746]
              | x -> x  in
            let uu____86748 =
              let uu____86759 =
                let uu____86768 =
                  let uu____86769 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____86769 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____86768  in
              [uu____86759]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____86748;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____86787 = lift_c1 ()  in solve_eq uu____86787 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___616_86796  ->
                       match uu___616_86796 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____86801 -> false))
                in
             let uu____86803 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____86833)::uu____86834,(wp2,uu____86836)::uu____86837)
                   -> (wp1, wp2)
               | uu____86910 ->
                   let uu____86935 =
                     let uu____86941 =
                       let uu____86943 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____86945 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____86943 uu____86945
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____86941)
                      in
                   FStar_Errors.raise_error uu____86935
                     env.FStar_TypeChecker_Env.range
                in
             match uu____86803 with
             | (wpc1,wpc2) ->
                 let uu____86955 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____86955
                 then
                   let uu____86960 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____86960 wl
                 else
                   (let uu____86964 =
                      let uu____86971 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____86971  in
                    match uu____86964 with
                    | (c2_decl,qualifiers) ->
                        let uu____86992 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____86992
                        then
                          let c1_repr =
                            let uu____86999 =
                              let uu____87000 =
                                let uu____87001 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____87001  in
                              let uu____87002 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____87000 uu____87002
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____86999
                             in
                          let c2_repr =
                            let uu____87004 =
                              let uu____87005 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____87006 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____87005 uu____87006
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____87004
                             in
                          let uu____87007 =
                            let uu____87012 =
                              let uu____87014 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____87016 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____87014 uu____87016
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____87012
                             in
                          (match uu____87007 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____87022 = attempt [prob] wl2  in
                               solve env uu____87022)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____87037 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____87037
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____87046 =
                                     let uu____87053 =
                                       let uu____87054 =
                                         let uu____87071 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____87074 =
                                           let uu____87085 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____87094 =
                                             let uu____87105 =
                                               let uu____87114 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____87114
                                                in
                                             [uu____87105]  in
                                           uu____87085 :: uu____87094  in
                                         (uu____87071, uu____87074)  in
                                       FStar_Syntax_Syntax.Tm_app uu____87054
                                        in
                                     FStar_Syntax_Syntax.mk uu____87053  in
                                   uu____87046 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____87163 =
                                    let uu____87170 =
                                      let uu____87171 =
                                        let uu____87188 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____87191 =
                                          let uu____87202 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____87211 =
                                            let uu____87222 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____87231 =
                                              let uu____87242 =
                                                let uu____87251 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____87251
                                                 in
                                              [uu____87242]  in
                                            uu____87222 :: uu____87231  in
                                          uu____87202 :: uu____87211  in
                                        (uu____87188, uu____87191)  in
                                      FStar_Syntax_Syntax.Tm_app uu____87171
                                       in
                                    FStar_Syntax_Syntax.mk uu____87170  in
                                  uu____87163 FStar_Pervasives_Native.None r)
                              in
                           (let uu____87305 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____87305
                            then
                              let uu____87310 =
                                let uu____87312 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____87312
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____87310
                            else ());
                           (let uu____87316 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____87316 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____87325 =
                                    let uu____87328 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _87331  ->
                                         FStar_Pervasives_Native.Some _87331)
                                      uu____87328
                                     in
                                  solve_prob orig uu____87325 [] wl1  in
                                let uu____87332 = attempt [base_prob] wl2  in
                                solve env uu____87332))))
           in
        let uu____87333 = FStar_Util.physical_equality c1 c2  in
        if uu____87333
        then
          let uu____87336 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____87336
        else
          ((let uu____87340 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____87340
            then
              let uu____87345 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____87347 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____87345
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____87347
            else ());
           (let uu____87352 =
              let uu____87361 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____87364 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____87361, uu____87364)  in
            match uu____87352 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____87382),FStar_Syntax_Syntax.Total
                    (t2,uu____87384)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____87401 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____87401 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____87403,FStar_Syntax_Syntax.Total uu____87404) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____87423),FStar_Syntax_Syntax.Total
                    (t2,uu____87425)) ->
                     let uu____87442 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____87442 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____87445),FStar_Syntax_Syntax.GTotal
                    (t2,uu____87447)) ->
                     let uu____87464 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____87464 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____87467),FStar_Syntax_Syntax.GTotal
                    (t2,uu____87469)) ->
                     let uu____87486 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____87486 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____87488,FStar_Syntax_Syntax.Comp uu____87489) ->
                     let uu____87498 =
                       let uu___4158_87501 = problem  in
                       let uu____87504 =
                         let uu____87505 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____87505
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4158_87501.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____87504;
                         FStar_TypeChecker_Common.relation =
                           (uu___4158_87501.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___4158_87501.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___4158_87501.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4158_87501.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4158_87501.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4158_87501.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4158_87501.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4158_87501.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____87498 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____87506,FStar_Syntax_Syntax.Comp uu____87507) ->
                     let uu____87516 =
                       let uu___4158_87519 = problem  in
                       let uu____87522 =
                         let uu____87523 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____87523
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4158_87519.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____87522;
                         FStar_TypeChecker_Common.relation =
                           (uu___4158_87519.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___4158_87519.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___4158_87519.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4158_87519.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4158_87519.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4158_87519.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4158_87519.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4158_87519.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____87516 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____87524,FStar_Syntax_Syntax.GTotal uu____87525) ->
                     let uu____87534 =
                       let uu___4170_87537 = problem  in
                       let uu____87540 =
                         let uu____87541 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____87541
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4170_87537.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___4170_87537.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___4170_87537.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____87540;
                         FStar_TypeChecker_Common.element =
                           (uu___4170_87537.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4170_87537.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4170_87537.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4170_87537.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4170_87537.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4170_87537.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____87534 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____87542,FStar_Syntax_Syntax.Total uu____87543) ->
                     let uu____87552 =
                       let uu___4170_87555 = problem  in
                       let uu____87558 =
                         let uu____87559 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____87559
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4170_87555.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___4170_87555.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___4170_87555.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____87558;
                         FStar_TypeChecker_Common.element =
                           (uu___4170_87555.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4170_87555.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4170_87555.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4170_87555.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4170_87555.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4170_87555.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____87552 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____87560,FStar_Syntax_Syntax.Comp uu____87561) ->
                     let uu____87562 =
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
                     if uu____87562
                     then
                       let uu____87565 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____87565 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____87572 =
                            let uu____87577 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____87577
                            then (c1_comp, c2_comp)
                            else
                              (let uu____87586 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____87587 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____87586, uu____87587))
                             in
                          match uu____87572 with
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
                           (let uu____87595 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____87595
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____87603 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____87603 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____87606 =
                                  let uu____87608 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____87610 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____87608 uu____87610
                                   in
                                giveup env uu____87606 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____87621 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____87621 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____87671 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____87671 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____87696 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____87727  ->
                match uu____87727 with
                | (u1,u2) ->
                    let uu____87735 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____87737 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____87735 uu____87737))
         in
      FStar_All.pipe_right uu____87696 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____87774,[])) when
          let uu____87801 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____87801 -> "{}"
      | uu____87804 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____87831 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____87831
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____87843 =
              FStar_List.map
                (fun uu____87856  ->
                   match uu____87856 with
                   | (uu____87863,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____87843 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____87874 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____87874 imps
  
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
                  let uu____87931 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____87931
                  then
                    let uu____87939 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____87941 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____87939
                      (rel_to_string rel) uu____87941
                  else "TOP"  in
                let uu____87947 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____87947 with
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
              let uu____88007 =
                let uu____88010 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _88013  -> FStar_Pervasives_Native.Some _88013)
                  uu____88010
                 in
              FStar_Syntax_Syntax.new_bv uu____88007 t1  in
            let uu____88014 =
              let uu____88019 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____88019
               in
            match uu____88014 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____88079 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____88079
         then
           let uu____88084 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____88084
         else ());
        (let uu____88091 =
           FStar_Util.record_time (fun uu____88098  -> solve env probs)  in
         match uu____88091 with
         | (sol,ms) ->
             ((let uu____88110 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____88110
               then
                 let uu____88115 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____88115
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____88128 =
                     FStar_Util.record_time
                       (fun uu____88135  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____88128 with
                    | ((),ms1) ->
                        ((let uu____88146 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____88146
                          then
                            let uu____88151 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____88151
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____88165 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____88165
                     then
                       let uu____88172 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____88172
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
          ((let uu____88199 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____88199
            then
              let uu____88204 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____88204
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____88211 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____88211
             then
               let uu____88216 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____88216
             else ());
            (let f2 =
               let uu____88222 =
                 let uu____88223 = FStar_Syntax_Util.unmeta f1  in
                 uu____88223.FStar_Syntax_Syntax.n  in
               match uu____88222 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____88227 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___4286_88228 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___4286_88228.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___4286_88228.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___4286_88228.FStar_TypeChecker_Env.implicits)
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
            let uu____88283 =
              let uu____88284 =
                let uu____88285 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _88286  ->
                       FStar_TypeChecker_Common.NonTrivial _88286)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____88285;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____88284  in
            FStar_All.pipe_left
              (fun _88293  -> FStar_Pervasives_Native.Some _88293)
              uu____88283
  
let with_guard_no_simp :
  'Auu____88303 .
    'Auu____88303 ->
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
            let uu____88326 =
              let uu____88327 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _88328  -> FStar_TypeChecker_Common.NonTrivial _88328)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____88327;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____88326
  
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
          (let uu____88361 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____88361
           then
             let uu____88366 = FStar_Syntax_Print.term_to_string t1  in
             let uu____88368 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____88366
               uu____88368
           else ());
          (let uu____88373 =
             let uu____88378 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____88378
              in
           match uu____88373 with
           | (prob,wl) ->
               let g =
                 let uu____88386 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____88396  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____88386  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____88432 = try_teq true env t1 t2  in
        match uu____88432 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____88437 = FStar_TypeChecker_Env.get_range env  in
              let uu____88438 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____88437 uu____88438);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____88446 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____88446
              then
                let uu____88451 = FStar_Syntax_Print.term_to_string t1  in
                let uu____88453 = FStar_Syntax_Print.term_to_string t2  in
                let uu____88455 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____88451
                  uu____88453 uu____88455
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
          let uu____88481 = FStar_TypeChecker_Env.get_range env  in
          let uu____88482 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____88481 uu____88482
  
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
        (let uu____88511 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____88511
         then
           let uu____88516 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____88518 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____88516 uu____88518
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____88529 =
           let uu____88536 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____88536 "sub_comp"
            in
         match uu____88529 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____88549 =
                 FStar_Util.record_time
                   (fun uu____88561  ->
                      let uu____88562 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____88573  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____88562)
                  in
               match uu____88549 with
               | (r,ms) ->
                   ((let uu____88604 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____88604
                     then
                       let uu____88609 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____88611 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____88613 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____88609 uu____88611
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____88613
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
      fun uu____88651  ->
        match uu____88651 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____88694 =
                 let uu____88700 =
                   let uu____88702 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____88704 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____88702 uu____88704
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____88700)  in
               let uu____88708 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____88694 uu____88708)
               in
            let equiv1 v1 v' =
              let uu____88721 =
                let uu____88726 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____88727 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____88726, uu____88727)  in
              match uu____88721 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____88747 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____88778 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____88778 with
                      | FStar_Syntax_Syntax.U_unif uu____88785 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____88814  ->
                                    match uu____88814 with
                                    | (u,v') ->
                                        let uu____88823 = equiv1 v1 v'  in
                                        if uu____88823
                                        then
                                          let uu____88828 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____88828 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____88849 -> []))
               in
            let uu____88854 =
              let wl =
                let uu___4377_88858 = empty_worklist env  in
                {
                  attempting = (uu___4377_88858.attempting);
                  wl_deferred = (uu___4377_88858.wl_deferred);
                  ctr = (uu___4377_88858.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4377_88858.smt_ok);
                  umax_heuristic_ok = (uu___4377_88858.umax_heuristic_ok);
                  tcenv = (uu___4377_88858.tcenv);
                  wl_implicits = (uu___4377_88858.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____88877  ->
                      match uu____88877 with
                      | (lb,v1) ->
                          let uu____88884 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____88884 with
                           | USolved wl1 -> ()
                           | uu____88887 -> fail1 lb v1)))
               in
            let rec check_ineq uu____88898 =
              match uu____88898 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____88910) -> true
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
                      uu____88934,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____88936,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____88947) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____88955,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____88964 -> false)
               in
            let uu____88970 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____88987  ->
                      match uu____88987 with
                      | (u,v1) ->
                          let uu____88995 = check_ineq (u, v1)  in
                          if uu____88995
                          then true
                          else
                            ((let uu____89003 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____89003
                              then
                                let uu____89008 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____89010 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____89008
                                  uu____89010
                              else ());
                             false)))
               in
            if uu____88970
            then ()
            else
              ((let uu____89020 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____89020
                then
                  ((let uu____89026 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____89026);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____89038 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____89038))
                else ());
               (let uu____89051 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____89051))
  
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
        let fail1 uu____89125 =
          match uu____89125 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4454_89151 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___4454_89151.attempting);
            wl_deferred = (uu___4454_89151.wl_deferred);
            ctr = (uu___4454_89151.ctr);
            defer_ok;
            smt_ok = (uu___4454_89151.smt_ok);
            umax_heuristic_ok = (uu___4454_89151.umax_heuristic_ok);
            tcenv = (uu___4454_89151.tcenv);
            wl_implicits = (uu___4454_89151.wl_implicits)
          }  in
        (let uu____89154 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____89154
         then
           let uu____89159 = FStar_Util.string_of_bool defer_ok  in
           let uu____89161 = wl_to_string wl  in
           let uu____89163 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____89159 uu____89161 uu____89163
         else ());
        (let g1 =
           let uu____89169 = solve_and_commit env wl fail1  in
           match uu____89169 with
           | FStar_Pervasives_Native.Some
               (uu____89176::uu____89177,uu____89178) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4469_89207 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___4469_89207.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___4469_89207.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____89208 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___4474_89217 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4474_89217.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4474_89217.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___4474_89217.FStar_TypeChecker_Env.implicits)
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
    let uu____89260 = FStar_ST.op_Bang last_proof_ns  in
    match uu____89260 with
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
            let uu___4493_89385 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___4493_89385.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___4493_89385.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___4493_89385.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____89386 =
            let uu____89388 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____89388  in
          if uu____89386
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____89400 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____89401 =
                       let uu____89403 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____89403
                        in
                     FStar_Errors.diag uu____89400 uu____89401)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____89411 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____89412 =
                        let uu____89414 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____89414
                         in
                      FStar_Errors.diag uu____89411 uu____89412)
                   else ();
                   (let uu____89420 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____89420
                      "discharge_guard'" env vc1);
                   (let uu____89422 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____89422 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____89431 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____89432 =
                                let uu____89434 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____89434
                                 in
                              FStar_Errors.diag uu____89431 uu____89432)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____89444 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____89445 =
                                let uu____89447 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____89447
                                 in
                              FStar_Errors.diag uu____89444 uu____89445)
                           else ();
                           (let vcs =
                              let uu____89461 = FStar_Options.use_tactics ()
                                 in
                              if uu____89461
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____89483  ->
                                     (let uu____89485 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____89485);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____89529  ->
                                              match uu____89529 with
                                              | (env1,goal,opts) ->
                                                  let uu____89545 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____89545, opts)))))
                              else
                                (let uu____89548 =
                                   let uu____89555 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____89555)  in
                                 [uu____89548])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____89588  ->
                                    match uu____89588 with
                                    | (env1,goal,opts) ->
                                        let uu____89598 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____89598 with
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
                                                (let uu____89610 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____89611 =
                                                   let uu____89613 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____89615 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____89613 uu____89615
                                                    in
                                                 FStar_Errors.diag
                                                   uu____89610 uu____89611)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____89622 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____89623 =
                                                   let uu____89625 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____89625
                                                    in
                                                 FStar_Errors.diag
                                                   uu____89622 uu____89623)
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
      let uu____89643 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____89643 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____89652 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____89652
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____89666 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____89666 with
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
        let uu____89696 = try_teq false env t1 t2  in
        match uu____89696 with
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
            let uu____89740 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____89740 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____89753 ->
                     let uu____89766 =
                       let uu____89767 = FStar_Syntax_Subst.compress r  in
                       uu____89767.FStar_Syntax_Syntax.n  in
                     (match uu____89766 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____89772) ->
                          unresolved ctx_u'
                      | uu____89789 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____89813 = acc  in
            match uu____89813 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____89832 = hd1  in
                     (match uu____89832 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____89843 = unresolved ctx_u  in
                             if uu____89843
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____89867 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____89867
                                     then
                                       let uu____89871 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____89871
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____89880 = teq_nosmt env1 t tm
                                          in
                                       match uu____89880 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Env.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4606_89890 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4606_89890.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4606_89890.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4606_89890.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4606_89890.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4606_89890.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4606_89890.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4606_89890.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4609_89898 = hd1  in
                                       {
                                         FStar_TypeChecker_Env.imp_reason =
                                           (uu___4609_89898.FStar_TypeChecker_Env.imp_reason);
                                         FStar_TypeChecker_Env.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Env.imp_tm =
                                           (uu___4609_89898.FStar_TypeChecker_Env.imp_tm);
                                         FStar_TypeChecker_Env.imp_range =
                                           (uu___4609_89898.FStar_TypeChecker_Env.imp_range)
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
                                    let uu___4613_89909 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4613_89909.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4613_89909.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4613_89909.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4613_89909.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4613_89909.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4613_89909.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4613_89909.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4613_89909.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4613_89909.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___4613_89909.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4613_89909.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4613_89909.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4613_89909.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4613_89909.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4613_89909.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4613_89909.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4613_89909.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4613_89909.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4613_89909.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4613_89909.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4613_89909.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4613_89909.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4613_89909.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4613_89909.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4613_89909.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4613_89909.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4613_89909.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4613_89909.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4613_89909.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4613_89909.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4613_89909.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4613_89909.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4613_89909.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4613_89909.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4613_89909.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4613_89909.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4613_89909.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4613_89909.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4613_89909.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4613_89909.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4613_89909.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4613_89909.FStar_TypeChecker_Env.nbe)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4618_89913 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4618_89913.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4618_89913.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4618_89913.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4618_89913.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4618_89913.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4618_89913.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4618_89913.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4618_89913.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4618_89913.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4618_89913.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___4618_89913.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4618_89913.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4618_89913.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4618_89913.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4618_89913.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4618_89913.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4618_89913.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4618_89913.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4618_89913.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4618_89913.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4618_89913.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4618_89913.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4618_89913.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4618_89913.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4618_89913.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4618_89913.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4618_89913.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4618_89913.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4618_89913.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4618_89913.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4618_89913.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4618_89913.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4618_89913.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4618_89913.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4618_89913.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4618_89913.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4618_89913.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4618_89913.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4618_89913.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4618_89913.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4618_89913.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4618_89913.FStar_TypeChecker_Env.nbe)
                                      }
                                    else env1  in
                                  (let uu____89918 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____89918
                                   then
                                     let uu____89923 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____89925 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____89927 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____89929 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____89923 uu____89925 uu____89927
                                       reason uu____89929
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4624_89936  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____89943 =
                                             let uu____89953 =
                                               let uu____89961 =
                                                 let uu____89963 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____89965 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____89967 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____89963 uu____89965
                                                   uu____89967
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____89961, r)
                                                in
                                             [uu____89953]  in
                                           FStar_Errors.add_errors
                                             uu____89943);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___4632_89987 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___4632_89987.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___4632_89987.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___4632_89987.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____89991 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____90002  ->
                                               let uu____90003 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____90005 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____90007 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____90003 uu____90005
                                                 reason uu____90007)) env2 g2
                                         true
                                        in
                                     match uu____89991 with
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
          let uu___4640_90015 = g  in
          let uu____90016 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4640_90015.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4640_90015.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___4640_90015.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____90016
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
        let uu____90059 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____90059 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____90060 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____90060
      | imp::uu____90062 ->
          let uu____90065 =
            let uu____90071 =
              let uu____90073 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____90075 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____90073 uu____90075 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____90071)
             in
          FStar_Errors.raise_error uu____90065
            imp.FStar_TypeChecker_Env.imp_range
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____90097 = teq_nosmt env t1 t2  in
        match uu____90097 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4662_90116 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___4662_90116.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___4662_90116.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___4662_90116.FStar_TypeChecker_Env.implicits)
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
        (let uu____90152 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____90152
         then
           let uu____90157 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____90159 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____90157
             uu____90159
         else ());
        (let uu____90164 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____90164 with
         | (prob,x,wl) ->
             let g =
               let uu____90183 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____90194  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____90183  in
             ((let uu____90215 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____90215
               then
                 let uu____90220 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____90222 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____90224 =
                   let uu____90226 = FStar_Util.must g  in
                   guard_to_string env uu____90226  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____90220 uu____90222 uu____90224
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
        let uu____90263 = check_subtyping env t1 t2  in
        match uu____90263 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____90282 =
              let uu____90283 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____90283 g  in
            FStar_Pervasives_Native.Some uu____90282
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____90302 = check_subtyping env t1 t2  in
        match uu____90302 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____90321 =
              let uu____90322 =
                let uu____90323 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____90323]  in
              FStar_TypeChecker_Env.close_guard env uu____90322 g  in
            FStar_Pervasives_Native.Some uu____90321
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____90361 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____90361
         then
           let uu____90366 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____90368 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____90366
             uu____90368
         else ());
        (let uu____90373 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____90373 with
         | (prob,x,wl) ->
             let g =
               let uu____90388 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____90399  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____90388  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____90423 =
                      let uu____90424 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____90424]  in
                    FStar_TypeChecker_Env.close_guard env uu____90423 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____90465 = subtype_nosmt env t1 t2  in
        match uu____90465 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  