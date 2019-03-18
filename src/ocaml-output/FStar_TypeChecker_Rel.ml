open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____60265 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____60300 -> false
  
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
                    let uu____60723 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____60723;
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
                     (let uu___656_60755 = wl  in
                      {
                        attempting = (uu___656_60755.attempting);
                        wl_deferred = (uu___656_60755.wl_deferred);
                        ctr = (uu___656_60755.ctr);
                        defer_ok = (uu___656_60755.defer_ok);
                        smt_ok = (uu___656_60755.smt_ok);
                        umax_heuristic_ok =
                          (uu___656_60755.umax_heuristic_ok);
                        tcenv = (uu___656_60755.tcenv);
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
            let uu___662_60788 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___662_60788.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___662_60788.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___662_60788.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___662_60788.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___662_60788.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___662_60788.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___662_60788.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___662_60788.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___662_60788.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___662_60788.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___662_60788.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___662_60788.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___662_60788.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___662_60788.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___662_60788.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___662_60788.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___662_60788.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___662_60788.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___662_60788.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___662_60788.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___662_60788.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___662_60788.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___662_60788.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___662_60788.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___662_60788.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___662_60788.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___662_60788.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___662_60788.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___662_60788.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___662_60788.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___662_60788.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___662_60788.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___662_60788.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___662_60788.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___662_60788.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___662_60788.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___662_60788.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___662_60788.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___662_60788.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___662_60788.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___662_60788.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___662_60788.FStar_TypeChecker_Env.nbe)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____60790 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____60790 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Env.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * Prims.string) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____60833 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____60869 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * Prims.string)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____60902 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____60913 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____60924 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___585_60942  ->
    match uu___585_60942 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____60954 = FStar_Syntax_Util.head_and_args t  in
    match uu____60954 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____61017 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____61019 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____61034 =
                     let uu____61036 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____61036  in
                   FStar_Util.format1 "@<%s>" uu____61034
                in
             let uu____61040 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____61017 uu____61019 uu____61040
         | uu____61043 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___586_61055  ->
      match uu___586_61055 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____61060 =
            let uu____61064 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____61066 =
              let uu____61070 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____61072 =
                let uu____61076 =
                  let uu____61080 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____61080]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____61076
                 in
              uu____61070 :: uu____61072  in
            uu____61064 :: uu____61066  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____61060
      | FStar_TypeChecker_Common.CProb p ->
          let uu____61091 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____61093 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____61095 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____61091
            uu____61093 (rel_to_string p.FStar_TypeChecker_Common.relation)
            uu____61095
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___587_61109  ->
      match uu___587_61109 with
      | UNIV (u,t) ->
          let x =
            let uu____61115 = FStar_Options.hide_uvar_nums ()  in
            if uu____61115
            then "?"
            else
              (let uu____61122 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____61122 FStar_Util.string_of_int)
             in
          let uu____61126 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____61126
      | TERM (u,t) ->
          let x =
            let uu____61133 = FStar_Options.hide_uvar_nums ()  in
            if uu____61133
            then "?"
            else
              (let uu____61140 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____61140 FStar_Util.string_of_int)
             in
          let uu____61144 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____61144
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____61163 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____61163 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____61184 =
      let uu____61188 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____61188
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____61184 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____61207 .
    (FStar_Syntax_Syntax.term * 'Auu____61207) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____61226 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____61247  ->
              match uu____61247 with
              | (x,uu____61254) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____61226 (FStar_String.concat " ")
  
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
        (let uu____61297 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____61297
         then
           let uu____61302 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____61302
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___588_61313  ->
    match uu___588_61313 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____61319 .
    'Auu____61319 FStar_TypeChecker_Common.problem ->
      'Auu____61319 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___722_61331 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___722_61331.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___722_61331.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___722_61331.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___722_61331.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___722_61331.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___722_61331.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___722_61331.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____61339 .
    'Auu____61339 FStar_TypeChecker_Common.problem ->
      'Auu____61339 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___589_61359  ->
    match uu___589_61359 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _61365  -> FStar_TypeChecker_Common.TProb _61365)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _61371  -> FStar_TypeChecker_Common.CProb _61371)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___590_61377  ->
    match uu___590_61377 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___734_61383 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___734_61383.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___734_61383.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___734_61383.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___734_61383.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___734_61383.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___734_61383.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___734_61383.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___734_61383.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___734_61383.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___738_61391 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___738_61391.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___738_61391.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___738_61391.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___738_61391.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___738_61391.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___738_61391.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___738_61391.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___738_61391.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___738_61391.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___591_61404  ->
      match uu___591_61404 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___592_61411  ->
    match uu___592_61411 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___593_61424  ->
    match uu___593_61424 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___594_61439  ->
    match uu___594_61439 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___595_61454  ->
    match uu___595_61454 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___596_61468  ->
    match uu___596_61468 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___597_61482  ->
    match uu___597_61482 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___598_61494  ->
    match uu___598_61494 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____61510 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____61510) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____61540 =
          let uu____61542 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____61542  in
        if uu____61540
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____61579)::bs ->
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
          let uu____61626 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____61650 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____61650]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____61626
      | FStar_TypeChecker_Common.CProb p ->
          let uu____61678 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____61702 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____61702]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____61678
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____61749 =
          let uu____61751 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____61751  in
        if uu____61749
        then ()
        else
          (let uu____61756 =
             let uu____61759 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____61759
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____61756 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____61808 =
          let uu____61810 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____61810  in
        if uu____61808
        then ()
        else
          (let uu____61815 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____61815)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____61835 =
        let uu____61837 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____61837  in
      if uu____61835
      then ()
      else
        (let msgf m =
           let uu____61851 =
             let uu____61853 =
               let uu____61855 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____61855 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____61853  in
           Prims.op_Hat msg uu____61851  in
         (let uu____61860 = msgf "scope"  in
          let uu____61863 = p_scope prob  in
          def_scope_wf uu____61860 (p_loc prob) uu____61863);
         (let uu____61875 = msgf "guard"  in
          def_check_scoped uu____61875 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____61882 = msgf "lhs"  in
                def_check_scoped uu____61882 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____61885 = msgf "rhs"  in
                def_check_scoped uu____61885 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____61892 = msgf "lhs"  in
                def_check_scoped_comp uu____61892 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____61895 = msgf "rhs"  in
                def_check_scoped_comp uu____61895 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___831_61916 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___831_61916.wl_deferred);
          ctr = (uu___831_61916.ctr);
          defer_ok = (uu___831_61916.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___831_61916.umax_heuristic_ok);
          tcenv = (uu___831_61916.tcenv);
          wl_implicits = (uu___831_61916.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____61924 .
    FStar_TypeChecker_Env.env ->
      ('Auu____61924 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___835_61947 = empty_worklist env  in
      let uu____61948 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____61948;
        wl_deferred = (uu___835_61947.wl_deferred);
        ctr = (uu___835_61947.ctr);
        defer_ok = (uu___835_61947.defer_ok);
        smt_ok = (uu___835_61947.smt_ok);
        umax_heuristic_ok = (uu___835_61947.umax_heuristic_ok);
        tcenv = (uu___835_61947.tcenv);
        wl_implicits = (uu___835_61947.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___840_61971 = wl  in
        {
          attempting = (uu___840_61971.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___840_61971.ctr);
          defer_ok = (uu___840_61971.defer_ok);
          smt_ok = (uu___840_61971.smt_ok);
          umax_heuristic_ok = (uu___840_61971.umax_heuristic_ok);
          tcenv = (uu___840_61971.tcenv);
          wl_implicits = (uu___840_61971.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___845_61999 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___845_61999.wl_deferred);
         ctr = (uu___845_61999.ctr);
         defer_ok = (uu___845_61999.defer_ok);
         smt_ok = (uu___845_61999.smt_ok);
         umax_heuristic_ok = (uu___845_61999.umax_heuristic_ok);
         tcenv = (uu___845_61999.tcenv);
         wl_implicits = (uu___845_61999.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____62013 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____62013 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____62047 = FStar_Syntax_Util.type_u ()  in
            match uu____62047 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____62059 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____62059 with
                 | (uu____62077,tt,wl1) ->
                     let uu____62080 = FStar_Syntax_Util.mk_eq2 u tt t1 t2
                        in
                     (uu____62080, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___599_62086  ->
    match uu___599_62086 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _62092  -> FStar_TypeChecker_Common.TProb _62092) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _62098  -> FStar_TypeChecker_Common.CProb _62098) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____62106 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____62106 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____62126  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____62168 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____62168 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____62168 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____62168 FStar_TypeChecker_Common.problem *
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
                        let uu____62255 =
                          let uu____62264 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____62264]  in
                        FStar_List.append scope uu____62255
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____62307 =
                      let uu____62310 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____62310  in
                    FStar_List.append uu____62307
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____62329 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____62329 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____62355 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____62355;
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
                  (let uu____62429 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____62429 with
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
                  (let uu____62517 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____62517 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____62555 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____62555 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____62555 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____62555 FStar_TypeChecker_Common.problem *
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
                          let uu____62623 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____62623]  in
                        let uu____62642 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____62642
                     in
                  let uu____62645 =
                    let uu____62652 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___928_62663 = wl  in
                       {
                         attempting = (uu___928_62663.attempting);
                         wl_deferred = (uu___928_62663.wl_deferred);
                         ctr = (uu___928_62663.ctr);
                         defer_ok = (uu___928_62663.defer_ok);
                         smt_ok = (uu___928_62663.smt_ok);
                         umax_heuristic_ok =
                           (uu___928_62663.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___928_62663.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____62652
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____62645 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____62681 =
                              let uu____62686 =
                                let uu____62687 =
                                  let uu____62696 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____62696
                                   in
                                [uu____62687]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____62686
                               in
                            uu____62681 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____62724 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____62724;
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
                let uu____62772 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____62772;
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
  'Auu____62787 .
    worklist ->
      'Auu____62787 FStar_TypeChecker_Common.problem ->
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
              let uu____62820 =
                let uu____62823 =
                  let uu____62824 =
                    let uu____62831 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____62831)  in
                  FStar_Syntax_Syntax.NT uu____62824  in
                [uu____62823]  in
              FStar_Syntax_Subst.subst uu____62820 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____62855 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____62855
        then
          let uu____62863 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____62866 = prob_to_string env d  in
          let uu____62868 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____62863 uu____62866 uu____62868 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____62884 -> failwith "impossible"  in
           let uu____62887 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____62903 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____62905 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____62903, uu____62905)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____62912 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____62914 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____62912, uu____62914)
              in
           match uu____62887 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___600_62942  ->
            match uu___600_62942 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____62954 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____62958 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____62958 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___601_62989  ->
           match uu___601_62989 with
           | UNIV uu____62992 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____62999 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____62999
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
        (fun uu___602_63027  ->
           match uu___602_63027 with
           | UNIV (u',t) ->
               let uu____63032 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____63032
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____63039 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____63051 =
        let uu____63052 =
          let uu____63053 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____63053
           in
        FStar_Syntax_Subst.compress uu____63052  in
      FStar_All.pipe_right uu____63051 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____63065 =
        let uu____63066 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____63066  in
      FStar_All.pipe_right uu____63065 FStar_Syntax_Util.unlazy_emb
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____63074 = FStar_Syntax_Util.head_and_args t  in
    match uu____63074 with
    | (h,uu____63093) ->
        let uu____63118 =
          let uu____63119 = FStar_Syntax_Subst.compress h  in
          uu____63119.FStar_Syntax_Syntax.n  in
        (match uu____63118 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____63124 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____63137 = should_strongly_reduce t  in
      if uu____63137
      then
        let uu____63140 =
          let uu____63141 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Reify;
              FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant] env t
             in
          FStar_Syntax_Subst.compress uu____63141  in
        FStar_All.pipe_right uu____63140 FStar_Syntax_Util.unlazy_emb
      else whnf' env t
  
let norm_arg :
  'Auu____63151 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____63151) ->
        (FStar_Syntax_Syntax.term * 'Auu____63151)
  =
  fun env  ->
    fun t  ->
      let uu____63174 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____63174, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____63226  ->
              match uu____63226 with
              | (x,imp) ->
                  let uu____63245 =
                    let uu___1025_63246 = x  in
                    let uu____63247 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1025_63246.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1025_63246.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____63247
                    }  in
                  (uu____63245, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____63271 = aux u3  in
            FStar_Syntax_Syntax.U_succ uu____63271
        | FStar_Syntax_Syntax.U_max us ->
            let uu____63275 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____63275
        | uu____63278 -> u2  in
      let uu____63279 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____63279
  
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
                (let uu____63400 = norm_refinement env t12  in
                 match uu____63400 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____63415;
                     FStar_Syntax_Syntax.vars = uu____63416;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____63440 =
                       let uu____63442 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____63444 = FStar_Syntax_Print.tag_of_term tt
                          in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____63442 uu____63444
                        in
                     failwith uu____63440)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____63460 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____63460
          | FStar_Syntax_Syntax.Tm_uinst uu____63461 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____63498 =
                   let uu____63499 = FStar_Syntax_Subst.compress t1'  in
                   uu____63499.FStar_Syntax_Syntax.n  in
                 match uu____63498 with
                 | FStar_Syntax_Syntax.Tm_refine uu____63514 -> aux true t1'
                 | uu____63522 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____63537 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____63568 =
                   let uu____63569 = FStar_Syntax_Subst.compress t1'  in
                   uu____63569.FStar_Syntax_Syntax.n  in
                 match uu____63568 with
                 | FStar_Syntax_Syntax.Tm_refine uu____63584 -> aux true t1'
                 | uu____63592 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____63607 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____63654 =
                   let uu____63655 = FStar_Syntax_Subst.compress t1'  in
                   uu____63655.FStar_Syntax_Syntax.n  in
                 match uu____63654 with
                 | FStar_Syntax_Syntax.Tm_refine uu____63670 -> aux true t1'
                 | uu____63678 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____63693 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____63708 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____63723 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____63738 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____63753 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____63782 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____63815 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____63836 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____63863 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____63891 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____63928 ->
              let uu____63935 =
                let uu____63937 = FStar_Syntax_Print.term_to_string t12  in
                let uu____63939 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____63937 uu____63939
                 in
              failwith uu____63935
          | FStar_Syntax_Syntax.Tm_ascribed uu____63954 ->
              let uu____63981 =
                let uu____63983 = FStar_Syntax_Print.term_to_string t12  in
                let uu____63985 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____63983 uu____63985
                 in
              failwith uu____63981
          | FStar_Syntax_Syntax.Tm_delayed uu____64000 ->
              let uu____64023 =
                let uu____64025 = FStar_Syntax_Print.term_to_string t12  in
                let uu____64027 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____64025 uu____64027
                 in
              failwith uu____64023
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____64042 =
                let uu____64044 = FStar_Syntax_Print.term_to_string t12  in
                let uu____64046 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____64044 uu____64046
                 in
              failwith uu____64042
           in
        let uu____64061 = whnf env t1  in aux false uu____64061
  
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
      let uu____64122 = base_and_refinement env t  in
      FStar_All.pipe_right uu____64122 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____64163 = FStar_Syntax_Syntax.null_bv t  in
    (uu____64163, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____64190 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____64190 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____64250  ->
    match uu____64250 with
    | (t_base,refopt) ->
        let uu____64281 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____64281 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____64323 =
      let uu____64327 =
        let uu____64330 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____64357  ->
                  match uu____64357 with | (uu____64366,uu____64367,x) -> x))
           in
        FStar_List.append wl.attempting uu____64330  in
      FStar_List.map (wl_prob_to_string wl) uu____64327  in
    FStar_All.pipe_right uu____64323 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____64390 .
    ('Auu____64390 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____64402  ->
    match uu____64402 with
    | (uu____64409,c,args) ->
        let uu____64412 = print_ctx_uvar c  in
        let uu____64414 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____64412 uu____64414
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____64424 = FStar_Syntax_Util.head_and_args t  in
    match uu____64424 with
    | (head1,_args) ->
        let uu____64468 =
          let uu____64469 = FStar_Syntax_Subst.compress head1  in
          uu____64469.FStar_Syntax_Syntax.n  in
        (match uu____64468 with
         | FStar_Syntax_Syntax.Tm_uvar uu____64473 -> true
         | uu____64487 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____64495 = FStar_Syntax_Util.head_and_args t  in
    match uu____64495 with
    | (head1,_args) ->
        let uu____64538 =
          let uu____64539 = FStar_Syntax_Subst.compress head1  in
          uu____64539.FStar_Syntax_Syntax.n  in
        (match uu____64538 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____64543) -> u
         | uu____64560 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____64585 = FStar_Syntax_Util.head_and_args t  in
      match uu____64585 with
      | (head1,args) ->
          let uu____64632 =
            let uu____64633 = FStar_Syntax_Subst.compress head1  in
            uu____64633.FStar_Syntax_Syntax.n  in
          (match uu____64632 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____64641)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____64674 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___603_64699  ->
                         match uu___603_64699 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____64704 =
                               let uu____64705 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____64705.FStar_Syntax_Syntax.n  in
                             (match uu____64704 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____64710 -> false)
                         | uu____64712 -> true))
                  in
               (match uu____64674 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____64737 =
                        FStar_List.collect
                          (fun uu___604_64749  ->
                             match uu___604_64749 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____64753 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____64753]
                             | uu____64754 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____64737 FStar_List.rev  in
                    let uu____64777 =
                      let uu____64784 =
                        let uu____64793 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___605_64815  ->
                                  match uu___605_64815 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____64819 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____64819]
                                  | uu____64820 -> []))
                           in
                        FStar_All.pipe_right uu____64793 FStar_List.rev  in
                      let uu____64843 =
                        let uu____64846 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____64846  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____64784 uu____64843
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____64777 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____64882  ->
                                match uu____64882 with
                                | (x,i) ->
                                    let uu____64901 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____64901, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____64932  ->
                                match uu____64932 with
                                | (a,i) ->
                                    let uu____64951 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____64951, i)) args_sol
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
           | uu____64973 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____64995 =
          let uu____65018 =
            let uu____65019 = FStar_Syntax_Subst.compress k  in
            uu____65019.FStar_Syntax_Syntax.n  in
          match uu____65018 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____65101 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____65101)
              else
                (let uu____65136 = FStar_Syntax_Util.abs_formals t  in
                 match uu____65136 with
                 | (ys',t1,uu____65169) ->
                     let uu____65174 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____65174))
          | uu____65213 ->
              let uu____65214 =
                let uu____65219 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____65219)  in
              ((ys, t), uu____65214)
           in
        match uu____64995 with
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
                 let uu____65314 = FStar_Syntax_Util.rename_binders xs ys1
                    in
                 FStar_Syntax_Subst.subst_comp uu____65314 c  in
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
               (let uu____65392 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____65392
                then
                  let uu____65397 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____65399 = print_ctx_uvar uv  in
                  let uu____65401 = FStar_Syntax_Print.term_to_string phi1
                     in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____65397 uu____65399 uu____65401
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____65410 =
                   let uu____65412 = FStar_Util.string_of_int (p_pid prob)
                      in
                   Prims.op_Hat "solve_prob'.sol." uu____65412  in
                 let uu____65415 =
                   let uu____65418 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____65418
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____65410 uu____65415 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____65451 =
               let uu____65452 =
                 let uu____65454 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____65456 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____65454 uu____65456
                  in
               failwith uu____65452  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____65522  ->
                       match uu____65522 with
                       | (a,i) ->
                           let uu____65543 =
                             let uu____65544 = FStar_Syntax_Subst.compress a
                                in
                             uu____65544.FStar_Syntax_Syntax.n  in
                           (match uu____65543 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____65570 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____65580 =
                 let uu____65582 = is_flex g  in
                 Prims.op_Negation uu____65582  in
               if uu____65580
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____65591 = destruct_flex_t g wl  in
                  match uu____65591 with
                  | ((uu____65596,uv1,args),wl1) ->
                      ((let uu____65601 = args_as_binders args  in
                        assign_solution uu____65601 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___1277_65603 = wl1  in
              {
                attempting = (uu___1277_65603.attempting);
                wl_deferred = (uu___1277_65603.wl_deferred);
                ctr = (wl1.ctr + (Prims.parse_int "1"));
                defer_ok = (uu___1277_65603.defer_ok);
                smt_ok = (uu___1277_65603.smt_ok);
                umax_heuristic_ok = (uu___1277_65603.umax_heuristic_ok);
                tcenv = (uu___1277_65603.tcenv);
                wl_implicits = (uu___1277_65603.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____65628 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____65628
         then
           let uu____65633 = FStar_Util.string_of_int pid  in
           let uu____65635 =
             let uu____65637 = FStar_List.map (uvi_to_string wl.tcenv) sol
                in
             FStar_All.pipe_right uu____65637 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____65633
             uu____65635
         else ());
        commit sol;
        (let uu___1285_65651 = wl  in
         {
           attempting = (uu___1285_65651.attempting);
           wl_deferred = (uu___1285_65651.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___1285_65651.defer_ok);
           smt_ok = (uu___1285_65651.smt_ok);
           umax_heuristic_ok = (uu___1285_65651.umax_heuristic_ok);
           tcenv = (uu___1285_65651.tcenv);
           wl_implicits = (uu___1285_65651.wl_implicits)
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
             | (uu____65717,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____65745 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____65745
              in
           (let uu____65751 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____65751
            then
              let uu____65756 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____65760 =
                let uu____65762 =
                  FStar_List.map (uvi_to_string wl.tcenv) uvis  in
                FStar_All.pipe_right uu____65762 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____65756
                uu____65760
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
        let uu____65797 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____65797 FStar_Util.set_elements  in
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
      let uu____65837 = occurs uk t  in
      match uu____65837 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____65876 =
                 let uu____65878 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____65880 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____65878 uu____65880
                  in
               FStar_Pervasives_Native.Some uu____65876)
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
            let uu____66000 = maximal_prefix bs_tail bs'_tail  in
            (match uu____66000 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____66051 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____66108  ->
             match uu____66108 with
             | (x,uu____66120) -> (FStar_Syntax_Syntax.Binding_var x) :: g1)
        g bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____66138 = FStar_List.last bs  in
      match uu____66138 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____66162) ->
          let uu____66173 =
            FStar_Util.prefix_until
              (fun uu___606_66188  ->
                 match uu___606_66188 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____66191 -> false) g
             in
          (match uu____66173 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____66205,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____66242 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____66242 with
        | (pfx,uu____66252) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____66264 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____66264 with
             | (uu____66272,src',wl1) ->
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
                 | uu____66386 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____66387 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____66451  ->
                  fun uu____66452  ->
                    match (uu____66451, uu____66452) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____66555 =
                          let uu____66557 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____66557
                           in
                        if uu____66555
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____66591 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____66591
                           then
                             let uu____66608 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____66608)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____66387 with | (isect,uu____66658) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____66694 'Auu____66695 .
    (FStar_Syntax_Syntax.bv * 'Auu____66694) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____66695) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____66753  ->
              fun uu____66754  ->
                match (uu____66753, uu____66754) with
                | ((a,uu____66773),(b,uu____66775)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____66791 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____66791) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____66822  ->
           match uu____66822 with
           | (y,uu____66829) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____66839 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____66839) Prims.list ->
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
                   let uu____67001 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____67001
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____67034 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____67086 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____67130 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____67151 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___607_67159  ->
    match uu___607_67159 with
    | MisMatch (d1,d2) ->
        let uu____67171 =
          let uu____67173 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____67175 =
            let uu____67177 =
              let uu____67179 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____67179 ")"  in
            Prims.op_Hat ") (" uu____67177  in
          Prims.op_Hat uu____67173 uu____67175  in
        Prims.op_Hat "MisMatch (" uu____67171
    | HeadMatch u ->
        let uu____67186 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____67186
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___608_67195  ->
    match uu___608_67195 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____67212 -> HeadMatch false
  
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
          let uu____67234 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____67234 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____67245 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____67269 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____67279 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____67306 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____67306
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____67307 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____67308 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____67309 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____67322 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____67336 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____67360) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____67366,uu____67367) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____67409) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____67434;
             FStar_Syntax_Syntax.index = uu____67435;
             FStar_Syntax_Syntax.sort = t2;_},uu____67437)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____67445 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____67446 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____67447 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____67462 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____67469 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____67489 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____67489
  
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
           { FStar_Syntax_Syntax.blob = uu____67508;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____67509;
             FStar_Syntax_Syntax.ltyp = uu____67510;
             FStar_Syntax_Syntax.rng = uu____67511;_},uu____67512)
            ->
            let uu____67523 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____67523 t21
        | (uu____67524,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____67525;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____67526;
             FStar_Syntax_Syntax.ltyp = uu____67527;
             FStar_Syntax_Syntax.rng = uu____67528;_})
            ->
            let uu____67539 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____67539
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____67551 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____67551
            then FullMatch
            else
              (let uu____67556 =
                 let uu____67565 =
                   let uu____67568 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____67568  in
                 let uu____67569 =
                   let uu____67572 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____67572  in
                 (uu____67565, uu____67569)  in
               MisMatch uu____67556)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____67578),FStar_Syntax_Syntax.Tm_uinst (g,uu____67580)) ->
            let uu____67589 = head_matches env f g  in
            FStar_All.pipe_right uu____67589 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____67590) -> HeadMatch true
        | (uu____67592,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____67596 = FStar_Const.eq_const c d  in
            if uu____67596
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____67606),FStar_Syntax_Syntax.Tm_uvar (uv',uu____67608)) ->
            let uu____67641 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____67641
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____67651),FStar_Syntax_Syntax.Tm_refine (y,uu____67653)) ->
            let uu____67662 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____67662 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____67664),uu____67665) ->
            let uu____67670 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____67670 head_match
        | (uu____67671,FStar_Syntax_Syntax.Tm_refine (x,uu____67673)) ->
            let uu____67678 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____67678 head_match
        | (FStar_Syntax_Syntax.Tm_type
           uu____67679,FStar_Syntax_Syntax.Tm_type uu____67680) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____67682,FStar_Syntax_Syntax.Tm_arrow uu____67683) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____67714),FStar_Syntax_Syntax.Tm_app
           (head',uu____67716)) ->
            let uu____67765 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____67765 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____67767),uu____67768) ->
            let uu____67793 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____67793 head_match
        | (uu____67794,FStar_Syntax_Syntax.Tm_app (head1,uu____67796)) ->
            let uu____67821 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____67821 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____67822,FStar_Syntax_Syntax.Tm_let
           uu____67823) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____67851,FStar_Syntax_Syntax.Tm_match uu____67852) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____67898,FStar_Syntax_Syntax.Tm_abs
           uu____67899) -> HeadMatch true
        | uu____67937 ->
            let uu____67942 =
              let uu____67951 = delta_depth_of_term env t11  in
              let uu____67954 = delta_depth_of_term env t21  in
              (uu____67951, uu____67954)  in
            MisMatch uu____67942
  
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
            (let uu____68020 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____68020
             then
               let uu____68025 = FStar_Syntax_Print.term_to_string t  in
               let uu____68027 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____68025 uu____68027
             else ());
            (let uu____68032 =
               let uu____68033 = FStar_Syntax_Util.un_uinst head1  in
               uu____68033.FStar_Syntax_Syntax.n  in
             match uu____68032 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____68039 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____68039 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____68053 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____68053
                        then
                          let uu____68058 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____68058
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____68063 ->
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
                      let uu____68080 =
                        let uu____68082 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____68082 = FStar_Syntax_Util.Equal  in
                      if uu____68080
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____68089 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____68089
                          then
                            let uu____68094 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____68096 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n"
                              uu____68094 uu____68096
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____68101 -> FStar_Pervasives_Native.None)
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
            (let uu____68253 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____68253
             then
               let uu____68258 = FStar_Syntax_Print.term_to_string t11  in
               let uu____68260 = FStar_Syntax_Print.term_to_string t21  in
               let uu____68262 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____68258
                 uu____68260 uu____68262
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____68290 =
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
               match uu____68290 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____68338 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____68338 with
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
                  uu____68376),uu____68377)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____68398 =
                      let uu____68407 = maybe_inline t11  in
                      let uu____68410 = maybe_inline t21  in
                      (uu____68407, uu____68410)  in
                    match uu____68398 with
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
                 (uu____68453,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  uu____68454))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____68475 =
                      let uu____68484 = maybe_inline t11  in
                      let uu____68487 = maybe_inline t21  in
                      (uu____68484, uu____68487)  in
                    match uu____68475 with
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
             | MisMatch uu____68542 -> fail1 n_delta r t11 t21
             | uu____68551 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____68566 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____68566
           then
             let uu____68571 = FStar_Syntax_Print.term_to_string t1  in
             let uu____68573 = FStar_Syntax_Print.term_to_string t2  in
             let uu____68575 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____68583 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____68600 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____68600
                    (fun uu____68635  ->
                       match uu____68635 with
                       | (t11,t21) ->
                           let uu____68643 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____68645 =
                             let uu____68647 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____68647  in
                           Prims.op_Hat uu____68643 uu____68645))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____68571 uu____68573 uu____68575 uu____68583
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____68664 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____68664 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___609_68679  ->
    match uu___609_68679 with
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
      let uu___1789_68728 = p  in
      let uu____68731 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____68732 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1789_68728.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____68731;
        FStar_TypeChecker_Common.relation =
          (uu___1789_68728.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____68732;
        FStar_TypeChecker_Common.element =
          (uu___1789_68728.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1789_68728.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1789_68728.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1789_68728.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1789_68728.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1789_68728.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____68747 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____68747
            (fun _68752  -> FStar_TypeChecker_Common.TProb _68752)
      | FStar_TypeChecker_Common.CProb uu____68753 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____68776 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____68776 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____68784 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____68784 with
           | (lh,lhs_args) ->
               let uu____68831 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____68831 with
                | (rh,rhs_args) ->
                    let uu____68878 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____68891,FStar_Syntax_Syntax.Tm_uvar uu____68892)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____68981 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____69008,uu____69009)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____69024,FStar_Syntax_Syntax.Tm_uvar uu____69025)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____69040,FStar_Syntax_Syntax.Tm_arrow
                         uu____69041) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_69071 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_69071.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_69071.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_69071.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_69071.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_69071.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_69071.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_69071.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_69071.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_69071.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____69074,FStar_Syntax_Syntax.Tm_type uu____69075)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_69091 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_69091.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_69091.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_69091.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_69091.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_69091.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_69091.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_69091.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_69091.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_69091.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____69094,FStar_Syntax_Syntax.Tm_uvar uu____69095)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_69111 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_69111.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_69111.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_69111.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_69111.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_69111.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_69111.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_69111.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_69111.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_69111.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____69114,FStar_Syntax_Syntax.Tm_uvar uu____69115)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____69130,uu____69131)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____69146,FStar_Syntax_Syntax.Tm_uvar uu____69147)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____69162,uu____69163) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____68878 with
                     | (rank,tp1) ->
                         let uu____69176 =
                           FStar_All.pipe_right
                             (let uu___1860_69180 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1860_69180.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1860_69180.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1860_69180.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1860_69180.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1860_69180.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1860_69180.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1860_69180.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1860_69180.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1860_69180.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _69183  ->
                                FStar_TypeChecker_Common.TProb _69183)
                            in
                         (rank, uu____69176))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____69187 =
            FStar_All.pipe_right
              (let uu___1864_69191 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1864_69191.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1864_69191.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1864_69191.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1864_69191.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1864_69191.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1864_69191.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1864_69191.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1864_69191.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1864_69191.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _69194  -> FStar_TypeChecker_Common.CProb _69194)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____69187)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____69254 probs =
      match uu____69254 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____69335 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____69356 = rank wl.tcenv hd1  in
               (match uu____69356 with
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
                      (let uu____69417 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____69422 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____69422)
                          in
                       if uu____69417
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
          let uu____69495 = FStar_Syntax_Util.head_and_args t  in
          match uu____69495 with
          | (hd1,uu____69514) ->
              let uu____69539 =
                let uu____69540 = FStar_Syntax_Subst.compress hd1  in
                uu____69540.FStar_Syntax_Syntax.n  in
              (match uu____69539 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____69545) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____69580  ->
                           match uu____69580 with
                           | (y,uu____69589) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____69612  ->
                                       match uu____69612 with
                                       | (x,uu____69621) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____69626 -> false)
           in
        let uu____69628 = rank tcenv p  in
        match uu____69628 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____69637 -> true
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
    match projectee with | UDeferred _0 -> true | uu____69674 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____69693 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____69713 -> false
  
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
                        let uu____69775 = FStar_Syntax_Util.univ_kernel u3
                           in
                        match uu____69775 with
                        | (k,uu____69783) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____69796 -> false)))
            | uu____69798 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____69850 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____69858 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____69858 = (Prims.parse_int "0")))
                           in
                        if uu____69850 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____69879 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____69887 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____69887 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____69879)
               in
            let uu____69891 = filter1 u12  in
            let uu____69894 = filter1 u22  in (uu____69891, uu____69894)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then UFailed "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____69929 = filter_out_common_univs us1 us2  in
                   (match uu____69929 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____69989 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____69989 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____69992 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          (let uu____70003 =
                             let uu____70005 =
                               FStar_Syntax_Print.univ_to_string u12  in
                             let uu____70007 =
                               FStar_Syntax_Print.univ_to_string u22  in
                             FStar_Util.format2
                               "Unable to unify universes: %s and %s"
                               uu____70005 uu____70007
                              in
                           UFailed uu____70003))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____70033 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____70033 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____70059 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____70059 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____70062 ->
                   let uu____70067 =
                     let uu____70069 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____70071 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format3
                       "Unable to unify universes: %s and %s (%s)"
                       uu____70069 uu____70071 msg
                      in
                   UFailed uu____70067)
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____70074,uu____70075) ->
              let uu____70077 =
                let uu____70079 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____70081 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____70079 uu____70081
                 in
              failwith uu____70077
          | (FStar_Syntax_Syntax.U_unknown ,uu____70084) ->
              let uu____70085 =
                let uu____70087 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____70089 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____70087 uu____70089
                 in
              failwith uu____70085
          | (uu____70092,FStar_Syntax_Syntax.U_bvar uu____70093) ->
              let uu____70095 =
                let uu____70097 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____70099 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____70097 uu____70099
                 in
              failwith uu____70095
          | (uu____70102,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____70103 =
                let uu____70105 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____70107 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____70105 uu____70107
                 in
              failwith uu____70103
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____70137 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____70137
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____70154 = occurs_univ v1 u3  in
              if uu____70154
              then
                let uu____70157 =
                  let uu____70159 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____70161 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____70159 uu____70161
                   in
                try_umax_components u11 u21 uu____70157
              else
                (let uu____70166 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____70166)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____70178 = occurs_univ v1 u3  in
              if uu____70178
              then
                let uu____70181 =
                  let uu____70183 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____70185 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____70183 uu____70185
                   in
                try_umax_components u11 u21 uu____70181
              else
                (let uu____70190 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____70190)
          | (FStar_Syntax_Syntax.U_max uu____70191,uu____70192) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____70200 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____70200
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____70206,FStar_Syntax_Syntax.U_max uu____70207) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____70215 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____70215
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____70221,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____70223,FStar_Syntax_Syntax.U_name uu____70224) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____70226) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____70228) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____70230,FStar_Syntax_Syntax.U_succ uu____70231) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____70233,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____70340 = bc1  in
      match uu____70340 with
      | (bs1,mk_cod1) ->
          let uu____70384 = bc2  in
          (match uu____70384 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____70495 = aux xs ys  in
                     (match uu____70495 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____70578 =
                       let uu____70585 = mk_cod1 xs  in ([], uu____70585)  in
                     let uu____70588 =
                       let uu____70595 = mk_cod2 ys  in ([], uu____70595)  in
                     (uu____70578, uu____70588)
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
                  let uu____70664 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____70664 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____70667 =
                    let uu____70668 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____70668 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____70667
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____70673 = has_type_guard t1 t2  in (uu____70673, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____70674 = has_type_guard t2 t1  in (uu____70674, wl)
  
let is_flex_pat :
  'Auu____70684 'Auu____70685 'Auu____70686 .
    ('Auu____70684 * 'Auu____70685 * 'Auu____70686 Prims.list) -> Prims.bool
  =
  fun uu___610_70700  ->
    match uu___610_70700 with
    | (uu____70709,uu____70710,[]) -> true
    | uu____70714 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____70747 = f  in
      match uu____70747 with
      | (uu____70754,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____70755;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____70756;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____70759;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____70760;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____70761;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____70762;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____70832  ->
                 match uu____70832 with
                 | (y,uu____70841) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____70995 =
                  let uu____71010 =
                    let uu____71013 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____71013  in
                  ((FStar_List.rev pat_binders), uu____71010)  in
                FStar_Pervasives_Native.Some uu____70995
            | (uu____71046,[]) ->
                let uu____71077 =
                  let uu____71092 =
                    let uu____71095 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____71095  in
                  ((FStar_List.rev pat_binders), uu____71092)  in
                FStar_Pervasives_Native.Some uu____71077
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____71186 =
                  let uu____71187 = FStar_Syntax_Subst.compress a  in
                  uu____71187.FStar_Syntax_Syntax.n  in
                (match uu____71186 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____71207 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____71207
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___2188_71237 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___2188_71237.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___2188_71237.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____71241 =
                            let uu____71242 =
                              let uu____71249 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____71249)  in
                            FStar_Syntax_Syntax.NT uu____71242  in
                          [uu____71241]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___2194_71265 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2194_71265.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2194_71265.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____71266 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____71306 =
                  let uu____71321 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____71321  in
                (match uu____71306 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____71396 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____71429 ->
               let uu____71430 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____71430 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____71752 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____71752
       then
         let uu____71757 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____71757
       else ());
      (let uu____71762 = next_prob probs  in
       match uu____71762 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___2219_71789 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___2219_71789.wl_deferred);
               ctr = (uu___2219_71789.ctr);
               defer_ok = (uu___2219_71789.defer_ok);
               smt_ok = (uu___2219_71789.smt_ok);
               umax_heuristic_ok = (uu___2219_71789.umax_heuristic_ok);
               tcenv = (uu___2219_71789.tcenv);
               wl_implicits = (uu___2219_71789.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____71798 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____71798
                 then
                   let uu____71801 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____71801
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
                           (let uu___2231_71813 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___2231_71813.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___2231_71813.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___2231_71813.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___2231_71813.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___2231_71813.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___2231_71813.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___2231_71813.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___2231_71813.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___2231_71813.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____71839 ->
                let uu____71850 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____71921  ->
                          match uu____71921 with
                          | (c,uu____71932,uu____71933) -> c < probs.ctr))
                   in
                (match uu____71850 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____71988 =
                            let uu____71993 =
                              FStar_List.map
                                (fun uu____72011  ->
                                   match uu____72011 with
                                   | (uu____72025,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____71993, (probs.wl_implicits))  in
                          Success uu____71988
                      | uu____72033 ->
                          let uu____72044 =
                            let uu___2249_72045 = probs  in
                            let uu____72046 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____72069  ->
                                      match uu____72069 with
                                      | (uu____72078,uu____72079,y) -> y))
                               in
                            {
                              attempting = uu____72046;
                              wl_deferred = rest;
                              ctr = (uu___2249_72045.ctr);
                              defer_ok = (uu___2249_72045.defer_ok);
                              smt_ok = (uu___2249_72045.smt_ok);
                              umax_heuristic_ok =
                                (uu___2249_72045.umax_heuristic_ok);
                              tcenv = (uu___2249_72045.tcenv);
                              wl_implicits = (uu___2249_72045.wl_implicits)
                            }  in
                          solve env uu____72044))))

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
            let uu____72090 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____72090 with
            | USolved wl1 ->
                let uu____72092 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____72092
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
                  let uu____72146 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____72146 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____72149 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____72162;
                  FStar_Syntax_Syntax.vars = uu____72163;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____72166;
                  FStar_Syntax_Syntax.vars = uu____72167;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____72180,uu____72181) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____72189,FStar_Syntax_Syntax.Tm_uinst uu____72190) ->
                failwith "Impossible: expect head symbols to match"
            | uu____72198 -> USolved wl

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
            ((let uu____72210 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____72210
              then
                let uu____72215 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____72215 msg
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
               let uu____72307 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____72307 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____72362 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____72362
                then
                  let uu____72367 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____72369 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____72367 uu____72369
                else ());
               (let uu____72374 = head_matches_delta env1 wl2 t1 t2  in
                match uu____72374 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____72420 = eq_prob t1 t2 wl2  in
                         (match uu____72420 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____72441 ->
                         let uu____72450 = eq_prob t1 t2 wl2  in
                         (match uu____72450 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____72500 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____72515 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____72516 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____72515, uu____72516)
                           | FStar_Pervasives_Native.None  ->
                               let uu____72521 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____72522 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____72521, uu____72522)
                            in
                         (match uu____72500 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____72553 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____72553 with
                                | (t1_hd,t1_args) ->
                                    let uu____72598 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____72598 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____72664 =
                                              let uu____72671 =
                                                let uu____72682 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____72682 :: t1_args  in
                                              let uu____72699 =
                                                let uu____72708 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____72708 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____72757  ->
                                                   fun uu____72758  ->
                                                     fun uu____72759  ->
                                                       match (uu____72757,
                                                               uu____72758,
                                                               uu____72759)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____72809),
                                                          (a2,uu____72811))
                                                           ->
                                                           let uu____72848 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____72848
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____72671
                                                uu____72699
                                               in
                                            match uu____72664 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___2403_72874 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___2403_72874.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___2403_72874.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___2403_72874.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____72886 =
                                                  solve env1 wl'  in
                                                (match uu____72886 with
                                                 | Success (uu____72889,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___2412_72893
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___2412_72893.attempting);
                                                            wl_deferred =
                                                              (uu___2412_72893.wl_deferred);
                                                            ctr =
                                                              (uu___2412_72893.ctr);
                                                            defer_ok =
                                                              (uu___2412_72893.defer_ok);
                                                            smt_ok =
                                                              (uu___2412_72893.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___2412_72893.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___2412_72893.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____72894 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____72927 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____72927 with
                                | (t1_base,p1_opt) ->
                                    let uu____72963 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____72963 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____73062 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____73062
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
                                               let uu____73115 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____73115
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
                                               let uu____73147 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____73147
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
                                               let uu____73179 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____73179
                                           | uu____73182 -> t_base  in
                                         let uu____73199 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____73199 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____73213 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____73213, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____73220 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____73220 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____73256 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____73256 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____73292 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____73292
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
                              let uu____73316 = combine t11 t21 wl2  in
                              (match uu____73316 with
                               | (t12,ps,wl3) ->
                                   ((let uu____73349 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____73349
                                     then
                                       let uu____73354 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____73354
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____73396 ts1 =
               match uu____73396 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____73459 = pairwise out t wl2  in
                        (match uu____73459 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____73495 =
               let uu____73506 = FStar_List.hd ts  in (uu____73506, [], wl1)
                in
             let uu____73515 = FStar_List.tl ts  in
             aux uu____73495 uu____73515  in
           let uu____73522 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____73522 with
           | (this_flex,this_rigid) ->
               let uu____73548 =
                 let uu____73549 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____73549.FStar_Syntax_Syntax.n  in
               (match uu____73548 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____73574 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____73574
                    then
                      let uu____73577 = destruct_flex_t this_flex wl  in
                      (match uu____73577 with
                       | (flex,wl1) ->
                           let uu____73584 = quasi_pattern env flex  in
                           (match uu____73584 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____73603 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____73603
                                  then
                                    let uu____73608 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____73608
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____73615 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2514_73618 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2514_73618.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2514_73618.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2514_73618.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2514_73618.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2514_73618.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2514_73618.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2514_73618.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2514_73618.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2514_73618.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____73615)
                | uu____73619 ->
                    ((let uu____73621 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____73621
                      then
                        let uu____73626 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____73626
                      else ());
                     (let uu____73631 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____73631 with
                      | (u,_args) ->
                          let uu____73674 =
                            let uu____73675 = FStar_Syntax_Subst.compress u
                               in
                            uu____73675.FStar_Syntax_Syntax.n  in
                          (match uu____73674 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____73703 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____73703 with
                                 | (u',uu____73722) ->
                                     let uu____73747 =
                                       let uu____73748 = whnf env u'  in
                                       uu____73748.FStar_Syntax_Syntax.n  in
                                     (match uu____73747 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____73770 -> false)
                                  in
                               let uu____73772 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___611_73795  ->
                                         match uu___611_73795 with
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
                                              | uu____73809 -> false)
                                         | uu____73813 -> false))
                                  in
                               (match uu____73772 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____73828 = whnf env this_rigid
                                         in
                                      let uu____73829 =
                                        FStar_List.collect
                                          (fun uu___612_73835  ->
                                             match uu___612_73835 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____73841 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____73841]
                                             | uu____73845 -> [])
                                          bounds_probs
                                         in
                                      uu____73828 :: uu____73829  in
                                    let uu____73846 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____73846 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____73879 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____73894 =
                                               let uu____73895 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____73895.FStar_Syntax_Syntax.n
                                                in
                                             match uu____73894 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____73907 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____73907)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____73918 -> bound  in
                                           let uu____73919 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____73919)  in
                                         (match uu____73879 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____73954 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____73954
                                                then
                                                  let wl'1 =
                                                    let uu___2574_73960 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2574_73960.wl_deferred);
                                                      ctr =
                                                        (uu___2574_73960.ctr);
                                                      defer_ok =
                                                        (uu___2574_73960.defer_ok);
                                                      smt_ok =
                                                        (uu___2574_73960.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2574_73960.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2574_73960.tcenv);
                                                      wl_implicits =
                                                        (uu___2574_73960.wl_implicits)
                                                    }  in
                                                  let uu____73961 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____73961
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____73967 =
                                                  solve_t env eq_prob
                                                    (let uu___2579_73969 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2579_73969.wl_deferred);
                                                       ctr =
                                                         (uu___2579_73969.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2579_73969.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2579_73969.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2579_73969.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____73967 with
                                                | Success (uu____73971,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2585_73974 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2585_73974.wl_deferred);
                                                        ctr =
                                                          (uu___2585_73974.ctr);
                                                        defer_ok =
                                                          (uu___2585_73974.defer_ok);
                                                        smt_ok =
                                                          (uu___2585_73974.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2585_73974.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2585_73974.tcenv);
                                                        wl_implicits =
                                                          (uu___2585_73974.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2588_73976 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2588_73976.attempting);
                                                        wl_deferred =
                                                          (uu___2588_73976.wl_deferred);
                                                        ctr =
                                                          (uu___2588_73976.ctr);
                                                        defer_ok =
                                                          (uu___2588_73976.defer_ok);
                                                        smt_ok =
                                                          (uu___2588_73976.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2588_73976.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2588_73976.tcenv);
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
                                                    let uu____73992 =
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
                                                    ((let uu____74006 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____74006
                                                      then
                                                        let uu____74011 =
                                                          let uu____74013 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____74013
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____74011
                                                      else ());
                                                     (let uu____74026 =
                                                        let uu____74041 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____74041)
                                                         in
                                                      match uu____74026 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____74063))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____74089 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____74089
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
                                                                  let uu____74109
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____74109))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____74134 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____74134
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
                                                                    let uu____74154
                                                                    =
                                                                    let uu____74159
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____74159
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____74154
                                                                    [] wl2
                                                                     in
                                                                  let uu____74165
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____74165))))
                                                      | uu____74166 ->
                                                          giveup env
                                                            (Prims.op_Hat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____74182 when flip ->
                               let uu____74183 =
                                 let uu____74185 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____74187 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____74185 uu____74187
                                  in
                               failwith uu____74183
                           | uu____74190 ->
                               let uu____74191 =
                                 let uu____74193 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____74195 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____74193 uu____74195
                                  in
                               failwith uu____74191)))))

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
                      (fun uu____74231  ->
                         match uu____74231 with
                         | (x,i) ->
                             let uu____74250 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____74250, i)) bs_lhs
                     in
                  let uu____74253 = lhs  in
                  match uu____74253 with
                  | (uu____74254,u_lhs,uu____74256) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____74353 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____74363 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____74363, univ)
                             in
                          match uu____74353 with
                          | (k,univ) ->
                              let uu____74370 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____74370 with
                               | (uu____74387,u,wl3) ->
                                   let uu____74390 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____74390, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____74416 =
                              let uu____74429 =
                                let uu____74440 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____74440 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____74491  ->
                                   fun uu____74492  ->
                                     match (uu____74491, uu____74492) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____74593 =
                                           let uu____74600 =
                                             let uu____74603 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____74603
                                              in
                                           copy_uvar u_lhs [] uu____74600 wl2
                                            in
                                         (match uu____74593 with
                                          | (uu____74632,t_a,wl3) ->
                                              let uu____74635 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____74635 with
                                               | (uu____74654,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____74429
                                ([], wl1)
                               in
                            (match uu____74416 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2698_74710 = ct  in
                                   let uu____74711 =
                                     let uu____74714 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____74714
                                      in
                                   let uu____74729 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2698_74710.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2698_74710.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____74711;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____74729;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2698_74710.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2701_74747 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2701_74747.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2701_74747.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____74750 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____74750 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____74812 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____74812 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____74823 =
                                          let uu____74828 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____74828)  in
                                        TERM uu____74823  in
                                      let uu____74829 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____74829 with
                                       | (sub_prob,wl3) ->
                                           let uu____74843 =
                                             let uu____74844 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____74844
                                              in
                                           solve env uu____74843))
                             | (x,imp)::formals2 ->
                                 let uu____74866 =
                                   let uu____74873 =
                                     let uu____74876 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____74876
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____74873 wl1
                                    in
                                 (match uu____74866 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____74897 =
                                          let uu____74900 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____74900
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____74897 u_x
                                         in
                                      let uu____74901 =
                                        let uu____74904 =
                                          let uu____74907 =
                                            let uu____74908 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____74908, imp)  in
                                          [uu____74907]  in
                                        FStar_List.append bs_terms
                                          uu____74904
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____74901 formals2 wl2)
                              in
                           let uu____74935 = occurs_check u_lhs arrow1  in
                           (match uu____74935 with
                            | (uu____74948,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____74964 =
                                    let uu____74966 = FStar_Option.get msg
                                       in
                                    Prims.op_Hat "occurs-check failed: "
                                      uu____74966
                                     in
                                  giveup_or_defer env orig wl uu____74964
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
              (let uu____74999 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____74999
               then
                 let uu____75004 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____75007 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____75004 (rel_to_string (p_rel orig)) uu____75007
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____75134 = rhs wl1 scope env1 subst1  in
                     (match uu____75134 with
                      | (rhs_prob,wl2) ->
                          ((let uu____75155 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____75155
                            then
                              let uu____75160 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____75160
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____75238 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____75238 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2770_75240 = hd1  in
                       let uu____75241 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2770_75240.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2770_75240.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____75241
                       }  in
                     let hd21 =
                       let uu___2773_75245 = hd2  in
                       let uu____75246 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2773_75245.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2773_75245.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____75246
                       }  in
                     let uu____75249 =
                       let uu____75254 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____75254
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____75249 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____75275 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____75275
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____75282 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____75282 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____75349 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____75349
                                  in
                               ((let uu____75367 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____75367
                                 then
                                   let uu____75372 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____75374 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____75372
                                     uu____75374
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____75407 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____75443 = aux wl [] env [] bs1 bs2  in
               match uu____75443 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____75498 = attempt sub_probs wl2  in
                   solve env uu____75498)

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
            let uu___2808_75519 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2808_75519.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2808_75519.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____75532 = try_solve env wl'  in
          match uu____75532 with
          | Success (uu____75533,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2817_75537 = wl  in
                  {
                    attempting = (uu___2817_75537.attempting);
                    wl_deferred = (uu___2817_75537.wl_deferred);
                    ctr = (uu___2817_75537.ctr);
                    defer_ok = (uu___2817_75537.defer_ok);
                    smt_ok = (uu___2817_75537.smt_ok);
                    umax_heuristic_ok = (uu___2817_75537.umax_heuristic_ok);
                    tcenv = (uu___2817_75537.tcenv);
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
        (let uu____75549 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____75549 wl)

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
              let uu____75563 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____75563 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____75597 = lhs1  in
              match uu____75597 with
              | (uu____75600,ctx_u,uu____75602) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____75610 ->
                        let uu____75611 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____75611 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____75660 = quasi_pattern env1 lhs1  in
              match uu____75660 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____75694) ->
                  let uu____75699 = lhs1  in
                  (match uu____75699 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____75714 = occurs_check ctx_u rhs1  in
                       (match uu____75714 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____75765 =
                                let uu____75773 =
                                  let uu____75775 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____75775
                                   in
                                FStar_Util.Inl uu____75773  in
                              (uu____75765, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____75803 =
                                 let uu____75805 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____75805  in
                               if uu____75803
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____75832 =
                                    let uu____75840 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____75840  in
                                  let uu____75846 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____75832, uu____75846)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____75890 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____75890 with
              | (rhs_hd,args) ->
                  let uu____75933 = FStar_Util.prefix args  in
                  (match uu____75933 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____76005 = lhs1  in
                       (match uu____76005 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____76009 =
                              let uu____76020 =
                                let uu____76027 =
                                  let uu____76030 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____76030
                                   in
                                copy_uvar u_lhs [] uu____76027 wl1  in
                              match uu____76020 with
                              | (uu____76057,t_last_arg,wl2) ->
                                  let uu____76060 =
                                    let uu____76067 =
                                      let uu____76068 =
                                        let uu____76077 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____76077]  in
                                      FStar_List.append bs_lhs uu____76068
                                       in
                                    copy_uvar u_lhs uu____76067 t_res_lhs wl2
                                     in
                                  (match uu____76060 with
                                   | (uu____76112,lhs',wl3) ->
                                       let uu____76115 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____76115 with
                                        | (uu____76132,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____76009 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____76153 =
                                     let uu____76154 =
                                       let uu____76159 =
                                         let uu____76160 =
                                           let uu____76163 =
                                             let uu____76168 =
                                               let uu____76169 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____76169]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____76168
                                              in
                                           uu____76163
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____76160
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____76159)  in
                                     TERM uu____76154  in
                                   [uu____76153]  in
                                 let uu____76194 =
                                   let uu____76201 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____76201 with
                                   | (p1,wl3) ->
                                       let uu____76221 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____76221 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____76194 with
                                  | (sub_probs,wl3) ->
                                      let uu____76253 =
                                        let uu____76254 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____76254  in
                                      solve env1 uu____76253))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____76288 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____76288 with
                | (uu____76306,args) ->
                    (match args with | [] -> false | uu____76342 -> true)
                 in
              let is_arrow rhs2 =
                let uu____76361 =
                  let uu____76362 = FStar_Syntax_Subst.compress rhs2  in
                  uu____76362.FStar_Syntax_Syntax.n  in
                match uu____76361 with
                | FStar_Syntax_Syntax.Tm_arrow uu____76366 -> true
                | uu____76382 -> false  in
              let uu____76384 = quasi_pattern env1 lhs1  in
              match uu____76384 with
              | FStar_Pervasives_Native.None  ->
                  let uu____76395 =
                    let uu____76397 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                      uu____76397
                     in
                  giveup_or_defer env1 orig1 wl1 uu____76395
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____76406 = is_app rhs1  in
                  if uu____76406
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____76411 = is_arrow rhs1  in
                     if uu____76411
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____76416 =
                          let uu____76418 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heuristic cannot solve %s; rhs not an app or arrow"
                            uu____76418
                           in
                        giveup_or_defer env1 orig1 wl1 uu____76416))
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
                let uu____76429 = lhs  in
                (match uu____76429 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____76433 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____76433 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____76451 =
                              let uu____76455 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____76455
                               in
                            FStar_All.pipe_right uu____76451
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____76476 = occurs_check ctx_uv rhs1  in
                          (match uu____76476 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____76505 =
                                   let uu____76507 = FStar_Option.get msg  in
                                   Prims.op_Hat "occurs-check failed: "
                                     uu____76507
                                    in
                                 giveup_or_defer env orig wl uu____76505
                               else
                                 (let uu____76513 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____76513
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____76520 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____76520
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____76524 =
                                         let uu____76526 =
                                           names_to_string1 fvs2  in
                                         let uu____76528 =
                                           names_to_string1 fvs1  in
                                         let uu____76530 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____76526 uu____76528
                                           uu____76530
                                          in
                                       giveup_or_defer env orig wl
                                         uu____76524)
                                    else first_order orig env wl lhs rhs1))
                      | uu____76542 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____76549 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____76549 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____76575 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____76575
                             | (FStar_Util.Inl msg,uu____76577) ->
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
                  (let uu____76622 =
                     let uu____76639 = quasi_pattern env lhs  in
                     let uu____76646 = quasi_pattern env rhs  in
                     (uu____76639, uu____76646)  in
                   match uu____76622 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____76689 = lhs  in
                       (match uu____76689 with
                        | ({ FStar_Syntax_Syntax.n = uu____76690;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____76692;_},u_lhs,uu____76694)
                            ->
                            let uu____76697 = rhs  in
                            (match uu____76697 with
                             | (uu____76698,u_rhs,uu____76700) ->
                                 let uu____76701 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____76701
                                 then
                                   let uu____76708 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____76708
                                 else
                                   (let uu____76711 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____76711 with
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
                                        let uu____76743 =
                                          let uu____76750 =
                                            let uu____76753 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____76753
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____76750
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____76743 with
                                         | (uu____76765,w,wl1) ->
                                             let w_app =
                                               let uu____76771 =
                                                 let uu____76776 =
                                                   FStar_List.map
                                                     (fun uu____76787  ->
                                                        match uu____76787
                                                        with
                                                        | (z,uu____76795) ->
                                                            let uu____76800 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____76800) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____76776
                                                  in
                                               uu____76771
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____76802 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____76802
                                               then
                                                 let uu____76807 =
                                                   let uu____76811 =
                                                     flex_t_to_string lhs  in
                                                   let uu____76813 =
                                                     let uu____76817 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____76819 =
                                                       let uu____76823 =
                                                         term_to_string w  in
                                                       let uu____76825 =
                                                         let uu____76829 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____76838 =
                                                           let uu____76842 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____76851 =
                                                             let uu____76855
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____76855]
                                                              in
                                                           uu____76842 ::
                                                             uu____76851
                                                            in
                                                         uu____76829 ::
                                                           uu____76838
                                                          in
                                                       uu____76823 ::
                                                         uu____76825
                                                        in
                                                     uu____76817 ::
                                                       uu____76819
                                                      in
                                                   uu____76811 :: uu____76813
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____76807
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____76872 =
                                                     let uu____76877 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____76877)  in
                                                   TERM uu____76872  in
                                                 let uu____76878 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____76878
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____76886 =
                                                        let uu____76891 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____76891)
                                                         in
                                                      TERM uu____76886  in
                                                    [s1; s2])
                                                  in
                                               let uu____76892 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____76892))))))
                   | uu____76893 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____76964 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____76964
            then
              let uu____76969 = FStar_Syntax_Print.term_to_string t1  in
              let uu____76971 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____76973 = FStar_Syntax_Print.term_to_string t2  in
              let uu____76975 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____76969 uu____76971 uu____76973 uu____76975
            else ());
           (let uu____76986 = FStar_Syntax_Util.head_and_args t1  in
            match uu____76986 with
            | (head1,args1) ->
                let uu____77029 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____77029 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____77099 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____77099 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              k false (defer "universe constraints" orig wl3))
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____77125 =
                         let uu____77127 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____77129 = args_to_string args1  in
                         let uu____77133 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____77135 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____77127 uu____77129 uu____77133 uu____77135
                          in
                       giveup env1 uu____77125 orig
                     else
                       (let uu____77142 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____77147 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____77147 = FStar_Syntax_Util.Equal)
                           in
                        if uu____77142
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___3066_77151 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___3066_77151.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___3066_77151.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___3066_77151.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___3066_77151.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___3066_77151.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___3066_77151.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___3066_77151.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___3066_77151.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____77161 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____77161
                                    else solve env1 wl2))
                        else
                          (let uu____77166 = base_and_refinement env1 t1  in
                           match uu____77166 with
                           | (base1,refinement1) ->
                               let uu____77191 = base_and_refinement env1 t2
                                  in
                               (match uu____77191 with
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
                                           let uu____77356 =
                                             FStar_List.fold_right
                                               (fun uu____77396  ->
                                                  fun uu____77397  ->
                                                    match (uu____77396,
                                                            uu____77397)
                                                    with
                                                    | (((a1,uu____77449),
                                                        (a2,uu____77451)),
                                                       (probs,wl3)) ->
                                                        let uu____77500 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____77500
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____77356 with
                                           | (subprobs,wl3) ->
                                               ((let uu____77543 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____77543
                                                 then
                                                   let uu____77548 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____77548
                                                 else ());
                                                (let uu____77554 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____77554
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
                                                    (let uu____77581 =
                                                       mk_sub_probs wl3  in
                                                     match uu____77581 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____77597 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____77597
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____77605 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____77605))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____77629 =
                                                    mk_sub_probs wl3  in
                                                  match uu____77629 with
                                                  | (subprobs,wl4) ->
                                                      let wl5 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          [] wl4
                                                         in
                                                      let uu____77643 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____77643)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____77669 =
                                           match uu____77669 with
                                           | (prob,reason) ->
                                               ((let uu____77680 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____77680
                                                 then
                                                   let uu____77685 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____77687 =
                                                     prob_to_string env2 prob
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____77685 uu____77687
                                                     reason
                                                 else ());
                                                (let uu____77692 =
                                                   let uu____77701 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____77704 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____77701, uu____77704)
                                                    in
                                                 match uu____77692 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____77717 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____77717 with
                                                      | (head1',uu____77735)
                                                          ->
                                                          let uu____77760 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____77760
                                                           with
                                                           | (head2',uu____77778)
                                                               ->
                                                               let uu____77803
                                                                 =
                                                                 let uu____77808
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____77809
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____77808,
                                                                   uu____77809)
                                                                  in
                                                               (match uu____77803
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____77811
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____77811
                                                                    then
                                                                    let uu____77816
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____77818
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____77820
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____77822
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____77816
                                                                    uu____77818
                                                                    uu____77820
                                                                    uu____77822
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____77827
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___3152_77835
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___3152_77835.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___3152_77835.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___3152_77835.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___3152_77835.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___3152_77835.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___3152_77835.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___3152_77835.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___3152_77835.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____77837
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____77837
                                                                    then
                                                                    let uu____77842
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____77842
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____77847 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____77859 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____77859 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____77867 =
                                             let uu____77868 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____77868.FStar_Syntax_Syntax.n
                                              in
                                           match uu____77867 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____77873 -> false  in
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
                                          | uu____77876 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____77879 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___3172_77915 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___3172_77915.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___3172_77915.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___3172_77915.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___3172_77915.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___3172_77915.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___3172_77915.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___3172_77915.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___3172_77915.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____77991 = destruct_flex_t scrutinee wl1  in
             match uu____77991 with
             | ((_t,uv,_args),wl2) ->
                 let uu____78002 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____78002 with
                  | (xs,pat_term,uu____78018,uu____78019) ->
                      let uu____78024 =
                        FStar_List.fold_left
                          (fun uu____78047  ->
                             fun x  ->
                               match uu____78047 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____78068 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____78068 with
                                    | (uu____78087,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____78024 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____78108 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____78108 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___3212_78125 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___3212_78125.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___3212_78125.umax_heuristic_ok);
                                    tcenv = (uu___3212_78125.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____78137 = solve env1 wl'  in
                                (match uu____78137 with
                                 | Success (uu____78140,imps) ->
                                     let wl'1 =
                                       let uu___3220_78143 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___3220_78143.wl_deferred);
                                         ctr = (uu___3220_78143.ctr);
                                         defer_ok =
                                           (uu___3220_78143.defer_ok);
                                         smt_ok = (uu___3220_78143.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___3220_78143.umax_heuristic_ok);
                                         tcenv = (uu___3220_78143.tcenv);
                                         wl_implicits =
                                           (uu___3220_78143.wl_implicits)
                                       }  in
                                     let uu____78144 = solve env1 wl'1  in
                                     (match uu____78144 with
                                      | Success (uu____78147,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___3228_78151 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___3228_78151.attempting);
                                                 wl_deferred =
                                                   (uu___3228_78151.wl_deferred);
                                                 ctr = (uu___3228_78151.ctr);
                                                 defer_ok =
                                                   (uu___3228_78151.defer_ok);
                                                 smt_ok =
                                                   (uu___3228_78151.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3228_78151.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3228_78151.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____78152 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____78159 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____78182 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____78182
                 then
                   let uu____78187 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____78189 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____78187 uu____78189
                 else ());
                (let uu____78194 =
                   let uu____78215 =
                     let uu____78224 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____78224)  in
                   let uu____78231 =
                     let uu____78240 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____78240)  in
                   (uu____78215, uu____78231)  in
                 match uu____78194 with
                 | ((uu____78270,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____78273;
                                   FStar_Syntax_Syntax.vars = uu____78274;_}),
                    (s,t)) ->
                     let uu____78345 =
                       let uu____78347 = is_flex scrutinee  in
                       Prims.op_Negation uu____78347  in
                     if uu____78345
                     then
                       ((let uu____78358 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____78358
                         then
                           let uu____78363 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____78363
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____78382 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____78382
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____78397 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____78397
                           then
                             let uu____78402 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____78404 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____78402 uu____78404
                           else ());
                          (let pat_discriminates uu___613_78429 =
                             match uu___613_78429 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____78445;
                                  FStar_Syntax_Syntax.p = uu____78446;_},FStar_Pervasives_Native.None
                                ,uu____78447) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____78461;
                                  FStar_Syntax_Syntax.p = uu____78462;_},FStar_Pervasives_Native.None
                                ,uu____78463) -> true
                             | uu____78490 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____78593 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____78593 with
                                       | (uu____78595,uu____78596,t') ->
                                           let uu____78614 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____78614 with
                                            | (FullMatch ,uu____78626) ->
                                                true
                                            | (HeadMatch
                                               uu____78640,uu____78641) ->
                                                true
                                            | uu____78656 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____78693 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____78693
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____78704 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____78704 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____78792,uu____78793) ->
                                       branches1
                                   | uu____78938 -> branches  in
                                 let uu____78993 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____79002 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____79002 with
                                        | (p,uu____79006,uu____79007) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _79036  -> FStar_Util.Inr _79036)
                                   uu____78993))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____79066 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____79066 with
                                | (p,uu____79075,e) ->
                                    ((let uu____79094 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____79094
                                      then
                                        let uu____79099 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____79101 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____79099 uu____79101
                                      else ());
                                     (let uu____79106 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _79121  -> FStar_Util.Inr _79121)
                                        uu____79106)))))
                 | ((s,t),(uu____79124,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____79127;
                                         FStar_Syntax_Syntax.vars =
                                           uu____79128;_}))
                     ->
                     let uu____79197 =
                       let uu____79199 = is_flex scrutinee  in
                       Prims.op_Negation uu____79199  in
                     if uu____79197
                     then
                       ((let uu____79210 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____79210
                         then
                           let uu____79215 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____79215
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____79234 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____79234
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____79249 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____79249
                           then
                             let uu____79254 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____79256 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____79254 uu____79256
                           else ());
                          (let pat_discriminates uu___613_79281 =
                             match uu___613_79281 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____79297;
                                  FStar_Syntax_Syntax.p = uu____79298;_},FStar_Pervasives_Native.None
                                ,uu____79299) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____79313;
                                  FStar_Syntax_Syntax.p = uu____79314;_},FStar_Pervasives_Native.None
                                ,uu____79315) -> true
                             | uu____79342 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____79445 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____79445 with
                                       | (uu____79447,uu____79448,t') ->
                                           let uu____79466 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____79466 with
                                            | (FullMatch ,uu____79478) ->
                                                true
                                            | (HeadMatch
                                               uu____79492,uu____79493) ->
                                                true
                                            | uu____79508 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____79545 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____79545
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____79556 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____79556 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____79644,uu____79645) ->
                                       branches1
                                   | uu____79790 -> branches  in
                                 let uu____79845 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____79854 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____79854 with
                                        | (p,uu____79858,uu____79859) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _79888  -> FStar_Util.Inr _79888)
                                   uu____79845))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____79918 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____79918 with
                                | (p,uu____79927,e) ->
                                    ((let uu____79946 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____79946
                                      then
                                        let uu____79951 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____79953 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____79951 uu____79953
                                      else ());
                                     (let uu____79958 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _79973  -> FStar_Util.Inr _79973)
                                        uu____79958)))))
                 | uu____79974 ->
                     ((let uu____79996 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____79996
                       then
                         let uu____80001 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____80003 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____80001 uu____80003
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____80049 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____80049
            then
              let uu____80054 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____80056 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____80058 = FStar_Syntax_Print.term_to_string t1  in
              let uu____80060 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____80054 uu____80056 uu____80058 uu____80060
            else ());
           (let uu____80065 = head_matches_delta env1 wl1 t1 t2  in
            match uu____80065 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____80096,uu____80097) ->
                     let rec may_relate head3 =
                       let uu____80125 =
                         let uu____80126 = FStar_Syntax_Subst.compress head3
                            in
                         uu____80126.FStar_Syntax_Syntax.n  in
                       match uu____80125 with
                       | FStar_Syntax_Syntax.Tm_name uu____80130 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____80132 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____80157 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____80157 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____80159 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____80162
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____80163 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____80166,uu____80167) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____80209) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____80215) ->
                           may_relate t
                       | uu____80220 -> false  in
                     let uu____80222 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____80222 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____80243 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____80243
                          then
                            let uu____80246 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____80246 with
                             | (guard,wl2) ->
                                 let uu____80253 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____80253)
                          else
                            (let uu____80256 =
                               let uu____80258 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____80260 =
                                 let uu____80262 =
                                   let uu____80266 =
                                     delta_depth_of_term env1 head1  in
                                   FStar_Util.bind_opt uu____80266
                                     (fun x  ->
                                        let uu____80273 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____80273)
                                    in
                                 FStar_Util.dflt "" uu____80262  in
                               let uu____80278 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               let uu____80280 =
                                 let uu____80282 =
                                   let uu____80286 =
                                     delta_depth_of_term env1 head2  in
                                   FStar_Util.bind_opt uu____80286
                                     (fun x  ->
                                        let uu____80293 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____80293)
                                    in
                                 FStar_Util.dflt "" uu____80282  in
                               FStar_Util.format4
                                 "head mismatch (%s (%s) vs %s (%s))"
                                 uu____80258 uu____80260 uu____80278
                                 uu____80280
                                in
                             giveup env1 uu____80256 orig))
                 | (HeadMatch (true ),uu____80299) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____80314 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____80314 with
                        | (guard,wl2) ->
                            let uu____80321 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____80321)
                     else
                       (let uu____80324 =
                          let uu____80326 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____80328 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____80326 uu____80328
                           in
                        giveup env1 uu____80324 orig)
                 | (uu____80331,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___3401_80345 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___3401_80345.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___3401_80345.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___3401_80345.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___3401_80345.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___3401_80345.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___3401_80345.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___3401_80345.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___3401_80345.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____80372 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____80372
          then
            let uu____80375 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____80375
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____80381 =
                let uu____80384 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____80384  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____80381 t1);
             (let uu____80403 =
                let uu____80406 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____80406  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____80403 t2);
             (let uu____80425 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____80425
              then
                let uu____80429 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____80431 =
                  let uu____80433 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____80435 =
                    let uu____80437 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____80437  in
                  Prims.op_Hat uu____80433 uu____80435  in
                let uu____80440 =
                  let uu____80442 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____80444 =
                    let uu____80446 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____80446  in
                  Prims.op_Hat uu____80442 uu____80444  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____80429 uu____80431 uu____80440
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____80453,uu____80454) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____80478,FStar_Syntax_Syntax.Tm_delayed uu____80479) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____80503,uu____80504) ->
                  let uu____80531 =
                    let uu___3432_80532 = problem  in
                    let uu____80533 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3432_80532.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____80533;
                      FStar_TypeChecker_Common.relation =
                        (uu___3432_80532.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3432_80532.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3432_80532.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3432_80532.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3432_80532.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3432_80532.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3432_80532.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3432_80532.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____80531 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____80534,uu____80535) ->
                  let uu____80542 =
                    let uu___3438_80543 = problem  in
                    let uu____80544 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3438_80543.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____80544;
                      FStar_TypeChecker_Common.relation =
                        (uu___3438_80543.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3438_80543.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3438_80543.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3438_80543.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3438_80543.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3438_80543.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3438_80543.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3438_80543.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____80542 wl
              | (uu____80545,FStar_Syntax_Syntax.Tm_ascribed uu____80546) ->
                  let uu____80573 =
                    let uu___3444_80574 = problem  in
                    let uu____80575 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3444_80574.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3444_80574.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3444_80574.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____80575;
                      FStar_TypeChecker_Common.element =
                        (uu___3444_80574.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3444_80574.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3444_80574.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3444_80574.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3444_80574.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3444_80574.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____80573 wl
              | (uu____80576,FStar_Syntax_Syntax.Tm_meta uu____80577) ->
                  let uu____80584 =
                    let uu___3450_80585 = problem  in
                    let uu____80586 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3450_80585.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3450_80585.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3450_80585.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____80586;
                      FStar_TypeChecker_Common.element =
                        (uu___3450_80585.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3450_80585.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3450_80585.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3450_80585.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3450_80585.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3450_80585.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____80584 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____80588),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____80590)) ->
                  let uu____80599 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____80599
              | (FStar_Syntax_Syntax.Tm_bvar uu____80600,uu____80601) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____80603,FStar_Syntax_Syntax.Tm_bvar uu____80604) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___614_80674 =
                    match uu___614_80674 with
                    | [] -> c
                    | bs ->
                        let uu____80702 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____80702
                     in
                  let uu____80713 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____80713 with
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
                                    let uu____80862 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____80862
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
                  let mk_t t l uu___615_80951 =
                    match uu___615_80951 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____80993 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____80993 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____81138 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____81139 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____81138
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____81139 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____81141,uu____81142) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____81173 -> true
                    | uu____81193 -> false  in
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
                      (let uu____81253 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3552_81261 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3552_81261.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3552_81261.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3552_81261.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3552_81261.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3552_81261.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3552_81261.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3552_81261.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3552_81261.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3552_81261.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___3552_81261.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3552_81261.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3552_81261.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3552_81261.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3552_81261.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3552_81261.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3552_81261.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3552_81261.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3552_81261.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3552_81261.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3552_81261.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3552_81261.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3552_81261.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3552_81261.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3552_81261.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3552_81261.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3552_81261.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3552_81261.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3552_81261.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3552_81261.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3552_81261.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3552_81261.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3552_81261.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3552_81261.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3552_81261.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3552_81261.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3552_81261.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3552_81261.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3552_81261.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3552_81261.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3552_81261.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____81253 with
                       | (uu____81266,ty,uu____81268) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____81277 =
                                 let uu____81278 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____81278.FStar_Syntax_Syntax.n  in
                               match uu____81277 with
                               | FStar_Syntax_Syntax.Tm_refine uu____81281 ->
                                   let uu____81288 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____81288
                               | uu____81289 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____81292 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____81292
                             then
                               let uu____81297 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____81299 =
                                 let uu____81301 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____81301
                                  in
                               let uu____81302 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____81297 uu____81299 uu____81302
                             else ());
                            r1))
                     in
                  let uu____81307 =
                    let uu____81324 = maybe_eta t1  in
                    let uu____81331 = maybe_eta t2  in
                    (uu____81324, uu____81331)  in
                  (match uu____81307 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3573_81373 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3573_81373.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3573_81373.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3573_81373.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3573_81373.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3573_81373.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3573_81373.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3573_81373.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3573_81373.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____81394 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____81394
                       then
                         let uu____81397 = destruct_flex_t not_abs wl  in
                         (match uu____81397 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_81414 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_81414.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_81414.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_81414.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_81414.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_81414.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_81414.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_81414.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_81414.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____81438 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____81438
                       then
                         let uu____81441 = destruct_flex_t not_abs wl  in
                         (match uu____81441 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_81458 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_81458.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_81458.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_81458.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_81458.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_81458.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_81458.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_81458.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_81458.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____81462 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____81480,FStar_Syntax_Syntax.Tm_abs uu____81481) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____81512 -> true
                    | uu____81532 -> false  in
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
                      (let uu____81592 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3552_81600 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3552_81600.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3552_81600.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3552_81600.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3552_81600.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3552_81600.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3552_81600.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3552_81600.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3552_81600.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3552_81600.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___3552_81600.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3552_81600.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3552_81600.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3552_81600.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3552_81600.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3552_81600.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3552_81600.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3552_81600.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3552_81600.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3552_81600.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3552_81600.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3552_81600.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3552_81600.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3552_81600.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3552_81600.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3552_81600.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3552_81600.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3552_81600.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3552_81600.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3552_81600.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3552_81600.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3552_81600.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3552_81600.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3552_81600.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3552_81600.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3552_81600.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3552_81600.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3552_81600.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3552_81600.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3552_81600.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3552_81600.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____81592 with
                       | (uu____81605,ty,uu____81607) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____81616 =
                                 let uu____81617 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____81617.FStar_Syntax_Syntax.n  in
                               match uu____81616 with
                               | FStar_Syntax_Syntax.Tm_refine uu____81620 ->
                                   let uu____81627 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____81627
                               | uu____81628 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____81631 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____81631
                             then
                               let uu____81636 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____81638 =
                                 let uu____81640 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____81640
                                  in
                               let uu____81641 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____81636 uu____81638 uu____81641
                             else ());
                            r1))
                     in
                  let uu____81646 =
                    let uu____81663 = maybe_eta t1  in
                    let uu____81670 = maybe_eta t2  in
                    (uu____81663, uu____81670)  in
                  (match uu____81646 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3573_81712 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3573_81712.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3573_81712.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3573_81712.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3573_81712.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3573_81712.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3573_81712.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3573_81712.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3573_81712.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____81733 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____81733
                       then
                         let uu____81736 = destruct_flex_t not_abs wl  in
                         (match uu____81736 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_81753 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_81753.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_81753.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_81753.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_81753.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_81753.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_81753.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_81753.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_81753.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____81777 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____81777
                       then
                         let uu____81780 = destruct_flex_t not_abs wl  in
                         (match uu____81780 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_81797 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_81797.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_81797.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_81797.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_81797.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_81797.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_81797.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_81797.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_81797.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____81801 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____81831 =
                    let uu____81836 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____81836 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3613_81864 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3613_81864.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3613_81864.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3615_81866 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3615_81866.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3615_81866.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____81867,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3613_81882 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3613_81882.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3613_81882.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3615_81884 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3615_81884.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3615_81884.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____81885 -> (x1, x2)  in
                  (match uu____81831 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____81904 = as_refinement false env t11  in
                       (match uu____81904 with
                        | (x12,phi11) ->
                            let uu____81912 = as_refinement false env t21  in
                            (match uu____81912 with
                             | (x22,phi21) ->
                                 ((let uu____81921 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____81921
                                   then
                                     ((let uu____81926 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____81928 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____81930 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____81926
                                         uu____81928 uu____81930);
                                      (let uu____81933 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____81935 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____81937 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____81933
                                         uu____81935 uu____81937))
                                   else ());
                                  (let uu____81942 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____81942 with
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
                                         let uu____82013 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____82013
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____82025 =
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
                                         (let uu____82038 =
                                            let uu____82041 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____82041
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____82038
                                            (p_guard base_prob));
                                         (let uu____82060 =
                                            let uu____82063 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____82063
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____82060
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____82082 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____82082)
                                          in
                                       let has_uvars =
                                         (let uu____82087 =
                                            let uu____82089 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____82089
                                             in
                                          Prims.op_Negation uu____82087) ||
                                           (let uu____82093 =
                                              let uu____82095 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____82095
                                               in
                                            Prims.op_Negation uu____82093)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____82099 =
                                           let uu____82104 =
                                             let uu____82113 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____82113]  in
                                           mk_t_problem wl1 uu____82104 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____82099 with
                                          | (ref_prob,wl2) ->
                                              let uu____82135 =
                                                solve env1
                                                  (let uu___3657_82137 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3657_82137.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3657_82137.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3657_82137.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3657_82137.tcenv);
                                                     wl_implicits =
                                                       (uu___3657_82137.wl_implicits)
                                                   })
                                                 in
                                              (match uu____82135 with
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
                                               | Success uu____82154 ->
                                                   let guard =
                                                     let uu____82162 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____82162
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___3668_82171 =
                                                       wl3  in
                                                     {
                                                       attempting =
                                                         (uu___3668_82171.attempting);
                                                       wl_deferred =
                                                         (uu___3668_82171.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            (Prims.parse_int "1"));
                                                       defer_ok =
                                                         (uu___3668_82171.defer_ok);
                                                       smt_ok =
                                                         (uu___3668_82171.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___3668_82171.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___3668_82171.tcenv);
                                                       wl_implicits =
                                                         (uu___3668_82171.wl_implicits)
                                                     }  in
                                                   let uu____82173 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____82173))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____82176,FStar_Syntax_Syntax.Tm_uvar uu____82177) ->
                  let uu____82202 = destruct_flex_t t1 wl  in
                  (match uu____82202 with
                   | (f1,wl1) ->
                       let uu____82209 = destruct_flex_t t2 wl1  in
                       (match uu____82209 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82216;
                    FStar_Syntax_Syntax.pos = uu____82217;
                    FStar_Syntax_Syntax.vars = uu____82218;_},uu____82219),FStar_Syntax_Syntax.Tm_uvar
                 uu____82220) ->
                  let uu____82269 = destruct_flex_t t1 wl  in
                  (match uu____82269 with
                   | (f1,wl1) ->
                       let uu____82276 = destruct_flex_t t2 wl1  in
                       (match uu____82276 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____82283,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82284;
                    FStar_Syntax_Syntax.pos = uu____82285;
                    FStar_Syntax_Syntax.vars = uu____82286;_},uu____82287))
                  ->
                  let uu____82336 = destruct_flex_t t1 wl  in
                  (match uu____82336 with
                   | (f1,wl1) ->
                       let uu____82343 = destruct_flex_t t2 wl1  in
                       (match uu____82343 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82350;
                    FStar_Syntax_Syntax.pos = uu____82351;
                    FStar_Syntax_Syntax.vars = uu____82352;_},uu____82353),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82354;
                    FStar_Syntax_Syntax.pos = uu____82355;
                    FStar_Syntax_Syntax.vars = uu____82356;_},uu____82357))
                  ->
                  let uu____82430 = destruct_flex_t t1 wl  in
                  (match uu____82430 with
                   | (f1,wl1) ->
                       let uu____82437 = destruct_flex_t t2 wl1  in
                       (match uu____82437 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____82444,uu____82445) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____82458 = destruct_flex_t t1 wl  in
                  (match uu____82458 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82465;
                    FStar_Syntax_Syntax.pos = uu____82466;
                    FStar_Syntax_Syntax.vars = uu____82467;_},uu____82468),uu____82469)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____82506 = destruct_flex_t t1 wl  in
                  (match uu____82506 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____82513,FStar_Syntax_Syntax.Tm_uvar uu____82514) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____82527,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82528;
                    FStar_Syntax_Syntax.pos = uu____82529;
                    FStar_Syntax_Syntax.vars = uu____82530;_},uu____82531))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____82568,FStar_Syntax_Syntax.Tm_arrow uu____82569) ->
                  solve_t' env
                    (let uu___3768_82597 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3768_82597.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3768_82597.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3768_82597.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3768_82597.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3768_82597.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3768_82597.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3768_82597.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3768_82597.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3768_82597.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82598;
                    FStar_Syntax_Syntax.pos = uu____82599;
                    FStar_Syntax_Syntax.vars = uu____82600;_},uu____82601),FStar_Syntax_Syntax.Tm_arrow
                 uu____82602) ->
                  solve_t' env
                    (let uu___3768_82654 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3768_82654.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3768_82654.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3768_82654.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3768_82654.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3768_82654.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3768_82654.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3768_82654.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3768_82654.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3768_82654.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____82655,FStar_Syntax_Syntax.Tm_uvar uu____82656) ->
                  let uu____82669 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____82669
              | (uu____82670,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82671;
                    FStar_Syntax_Syntax.pos = uu____82672;
                    FStar_Syntax_Syntax.vars = uu____82673;_},uu____82674))
                  ->
                  let uu____82711 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____82711
              | (FStar_Syntax_Syntax.Tm_uvar uu____82712,uu____82713) ->
                  let uu____82726 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____82726
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82727;
                    FStar_Syntax_Syntax.pos = uu____82728;
                    FStar_Syntax_Syntax.vars = uu____82729;_},uu____82730),uu____82731)
                  ->
                  let uu____82768 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____82768
              | (FStar_Syntax_Syntax.Tm_refine uu____82769,uu____82770) ->
                  let t21 =
                    let uu____82778 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____82778  in
                  solve_t env
                    (let uu___3803_82804 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3803_82804.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3803_82804.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3803_82804.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3803_82804.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3803_82804.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3803_82804.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3803_82804.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3803_82804.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3803_82804.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____82805,FStar_Syntax_Syntax.Tm_refine uu____82806) ->
                  let t11 =
                    let uu____82814 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____82814  in
                  solve_t env
                    (let uu___3810_82840 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3810_82840.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3810_82840.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3810_82840.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3810_82840.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3810_82840.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3810_82840.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3810_82840.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3810_82840.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3810_82840.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____82922 =
                    let uu____82923 = guard_of_prob env wl problem t1 t2  in
                    match uu____82923 with
                    | (guard,wl1) ->
                        let uu____82930 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____82930
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____83149 = br1  in
                        (match uu____83149 with
                         | (p1,w1,uu____83178) ->
                             let uu____83195 = br2  in
                             (match uu____83195 with
                              | (p2,w2,uu____83218) ->
                                  let uu____83223 =
                                    let uu____83225 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____83225  in
                                  if uu____83223
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____83252 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____83252 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____83289 = br2  in
                                         (match uu____83289 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____83322 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____83322
                                                 in
                                              let uu____83327 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____83358,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____83379) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____83438 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____83438 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____83327
                                                (fun uu____83510  ->
                                                   match uu____83510 with
                                                   | (wprobs,wl2) ->
                                                       let uu____83547 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____83547
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____83568
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____83568
                                                              then
                                                                let uu____83573
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____83575
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____83573
                                                                  uu____83575
                                                              else ());
                                                             (let uu____83581
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____83581
                                                                (fun
                                                                   uu____83617
                                                                    ->
                                                                   match uu____83617
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
                    | uu____83746 -> FStar_Pervasives_Native.None  in
                  let uu____83787 = solve_branches wl brs1 brs2  in
                  (match uu____83787 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____83838 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____83838 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____83872 =
                                FStar_List.map
                                  (fun uu____83884  ->
                                     match uu____83884 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____83872  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____83893 =
                              let uu____83894 =
                                let uu____83895 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____83895
                                  (let uu___3909_83903 = wl3  in
                                   {
                                     attempting =
                                       (uu___3909_83903.attempting);
                                     wl_deferred =
                                       (uu___3909_83903.wl_deferred);
                                     ctr = (uu___3909_83903.ctr);
                                     defer_ok = (uu___3909_83903.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3909_83903.umax_heuristic_ok);
                                     tcenv = (uu___3909_83903.tcenv);
                                     wl_implicits =
                                       (uu___3909_83903.wl_implicits)
                                   })
                                 in
                              solve env uu____83894  in
                            (match uu____83893 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____83908 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____83915,uu____83916) ->
                  let head1 =
                    let uu____83940 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____83940
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____83986 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____83986
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____84032 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____84032
                    then
                      let uu____84036 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____84038 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____84040 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____84036 uu____84038 uu____84040
                    else ());
                   (let no_free_uvars t =
                      (let uu____84054 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____84054) &&
                        (let uu____84058 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____84058)
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
                      let uu____84075 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____84075 = FStar_Syntax_Util.Equal  in
                    let uu____84076 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____84076
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____84080 = equal t1 t2  in
                         (if uu____84080
                          then
                            let uu____84083 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____84083
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____84088 =
                            let uu____84095 = equal t1 t2  in
                            if uu____84095
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____84108 = mk_eq2 wl env orig t1 t2  in
                               match uu____84108 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____84088 with
                          | (guard,wl1) ->
                              let uu____84129 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____84129))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____84132,uu____84133) ->
                  let head1 =
                    let uu____84141 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84141
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84187 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84187
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____84233 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____84233
                    then
                      let uu____84237 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____84239 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____84241 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____84237 uu____84239 uu____84241
                    else ());
                   (let no_free_uvars t =
                      (let uu____84255 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____84255) &&
                        (let uu____84259 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____84259)
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
                      let uu____84276 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____84276 = FStar_Syntax_Util.Equal  in
                    let uu____84277 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____84277
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____84281 = equal t1 t2  in
                         (if uu____84281
                          then
                            let uu____84284 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____84284
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____84289 =
                            let uu____84296 = equal t1 t2  in
                            if uu____84296
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____84309 = mk_eq2 wl env orig t1 t2  in
                               match uu____84309 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____84289 with
                          | (guard,wl1) ->
                              let uu____84330 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____84330))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____84333,uu____84334) ->
                  let head1 =
                    let uu____84336 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84336
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84382 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84382
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____84428 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____84428
                    then
                      let uu____84432 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____84434 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____84436 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____84432 uu____84434 uu____84436
                    else ());
                   (let no_free_uvars t =
                      (let uu____84450 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____84450) &&
                        (let uu____84454 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____84454)
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
                      let uu____84471 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____84471 = FStar_Syntax_Util.Equal  in
                    let uu____84472 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____84472
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____84476 = equal t1 t2  in
                         (if uu____84476
                          then
                            let uu____84479 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____84479
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____84484 =
                            let uu____84491 = equal t1 t2  in
                            if uu____84491
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____84504 = mk_eq2 wl env orig t1 t2  in
                               match uu____84504 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____84484 with
                          | (guard,wl1) ->
                              let uu____84525 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____84525))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____84528,uu____84529) ->
                  let head1 =
                    let uu____84531 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84531
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84577 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84577
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____84623 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____84623
                    then
                      let uu____84627 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____84629 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____84631 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____84627 uu____84629 uu____84631
                    else ());
                   (let no_free_uvars t =
                      (let uu____84645 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____84645) &&
                        (let uu____84649 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____84649)
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
                      let uu____84666 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____84666 = FStar_Syntax_Util.Equal  in
                    let uu____84667 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____84667
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____84671 = equal t1 t2  in
                         (if uu____84671
                          then
                            let uu____84674 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____84674
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____84679 =
                            let uu____84686 = equal t1 t2  in
                            if uu____84686
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____84699 = mk_eq2 wl env orig t1 t2  in
                               match uu____84699 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____84679 with
                          | (guard,wl1) ->
                              let uu____84720 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____84720))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____84723,uu____84724) ->
                  let head1 =
                    let uu____84726 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84726
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84772 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84772
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____84818 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____84818
                    then
                      let uu____84822 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____84824 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____84826 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____84822 uu____84824 uu____84826
                    else ());
                   (let no_free_uvars t =
                      (let uu____84840 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____84840) &&
                        (let uu____84844 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____84844)
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
                      let uu____84861 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____84861 = FStar_Syntax_Util.Equal  in
                    let uu____84862 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____84862
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____84866 = equal t1 t2  in
                         (if uu____84866
                          then
                            let uu____84869 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____84869
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____84874 =
                            let uu____84881 = equal t1 t2  in
                            if uu____84881
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____84894 = mk_eq2 wl env orig t1 t2  in
                               match uu____84894 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____84874 with
                          | (guard,wl1) ->
                              let uu____84915 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____84915))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____84918,uu____84919) ->
                  let head1 =
                    let uu____84937 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84937
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84983 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84983
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85029 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85029
                    then
                      let uu____85033 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85035 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85037 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85033 uu____85035 uu____85037
                    else ());
                   (let no_free_uvars t =
                      (let uu____85051 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85051) &&
                        (let uu____85055 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85055)
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
                      let uu____85072 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85072 = FStar_Syntax_Util.Equal  in
                    let uu____85073 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85073
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85077 = equal t1 t2  in
                         (if uu____85077
                          then
                            let uu____85080 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85080
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85085 =
                            let uu____85092 = equal t1 t2  in
                            if uu____85092
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85105 = mk_eq2 wl env orig t1 t2  in
                               match uu____85105 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85085 with
                          | (guard,wl1) ->
                              let uu____85126 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85126))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____85129,FStar_Syntax_Syntax.Tm_match uu____85130) ->
                  let head1 =
                    let uu____85154 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85154
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85200 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85200
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85246 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85246
                    then
                      let uu____85250 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85252 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85254 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85250 uu____85252 uu____85254
                    else ());
                   (let no_free_uvars t =
                      (let uu____85268 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85268) &&
                        (let uu____85272 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85272)
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
                      let uu____85289 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85289 = FStar_Syntax_Util.Equal  in
                    let uu____85290 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85290
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85294 = equal t1 t2  in
                         (if uu____85294
                          then
                            let uu____85297 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85297
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85302 =
                            let uu____85309 = equal t1 t2  in
                            if uu____85309
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85322 = mk_eq2 wl env orig t1 t2  in
                               match uu____85322 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85302 with
                          | (guard,wl1) ->
                              let uu____85343 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85343))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____85346,FStar_Syntax_Syntax.Tm_uinst uu____85347) ->
                  let head1 =
                    let uu____85355 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85355
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85395 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85395
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85435 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85435
                    then
                      let uu____85439 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85441 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85443 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85439 uu____85441 uu____85443
                    else ());
                   (let no_free_uvars t =
                      (let uu____85457 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85457) &&
                        (let uu____85461 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85461)
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
                      let uu____85478 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85478 = FStar_Syntax_Util.Equal  in
                    let uu____85479 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85479
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85483 = equal t1 t2  in
                         (if uu____85483
                          then
                            let uu____85486 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85486
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85491 =
                            let uu____85498 = equal t1 t2  in
                            if uu____85498
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85511 = mk_eq2 wl env orig t1 t2  in
                               match uu____85511 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85491 with
                          | (guard,wl1) ->
                              let uu____85532 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85532))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____85535,FStar_Syntax_Syntax.Tm_name uu____85536) ->
                  let head1 =
                    let uu____85538 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85538
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85578 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85578
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85618 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85618
                    then
                      let uu____85622 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85624 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85626 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85622 uu____85624 uu____85626
                    else ());
                   (let no_free_uvars t =
                      (let uu____85640 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85640) &&
                        (let uu____85644 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85644)
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
                      let uu____85661 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85661 = FStar_Syntax_Util.Equal  in
                    let uu____85662 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85662
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85666 = equal t1 t2  in
                         (if uu____85666
                          then
                            let uu____85669 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85669
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85674 =
                            let uu____85681 = equal t1 t2  in
                            if uu____85681
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85694 = mk_eq2 wl env orig t1 t2  in
                               match uu____85694 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85674 with
                          | (guard,wl1) ->
                              let uu____85715 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85715))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____85718,FStar_Syntax_Syntax.Tm_constant uu____85719) ->
                  let head1 =
                    let uu____85721 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85721
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85761 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85761
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85801 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85801
                    then
                      let uu____85805 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85807 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85809 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85805 uu____85807 uu____85809
                    else ());
                   (let no_free_uvars t =
                      (let uu____85823 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85823) &&
                        (let uu____85827 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85827)
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
                      let uu____85844 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85844 = FStar_Syntax_Util.Equal  in
                    let uu____85845 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85845
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85849 = equal t1 t2  in
                         (if uu____85849
                          then
                            let uu____85852 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85852
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85857 =
                            let uu____85864 = equal t1 t2  in
                            if uu____85864
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85877 = mk_eq2 wl env orig t1 t2  in
                               match uu____85877 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85857 with
                          | (guard,wl1) ->
                              let uu____85898 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85898))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____85901,FStar_Syntax_Syntax.Tm_fvar uu____85902) ->
                  let head1 =
                    let uu____85904 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85904
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85944 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85944
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85984 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85984
                    then
                      let uu____85988 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85990 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85992 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85988 uu____85990 uu____85992
                    else ());
                   (let no_free_uvars t =
                      (let uu____86006 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____86006) &&
                        (let uu____86010 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____86010)
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
                      let uu____86027 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____86027 = FStar_Syntax_Util.Equal  in
                    let uu____86028 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____86028
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____86032 = equal t1 t2  in
                         (if uu____86032
                          then
                            let uu____86035 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____86035
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____86040 =
                            let uu____86047 = equal t1 t2  in
                            if uu____86047
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____86060 = mk_eq2 wl env orig t1 t2  in
                               match uu____86060 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____86040 with
                          | (guard,wl1) ->
                              let uu____86081 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____86081))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____86084,FStar_Syntax_Syntax.Tm_app uu____86085) ->
                  let head1 =
                    let uu____86103 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____86103
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____86143 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____86143
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____86183 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____86183
                    then
                      let uu____86187 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____86189 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____86191 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____86187 uu____86189 uu____86191
                    else ());
                   (let no_free_uvars t =
                      (let uu____86205 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____86205) &&
                        (let uu____86209 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____86209)
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
                      let uu____86226 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____86226 = FStar_Syntax_Util.Equal  in
                    let uu____86227 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____86227
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____86231 = equal t1 t2  in
                         (if uu____86231
                          then
                            let uu____86234 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____86234
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____86239 =
                            let uu____86246 = equal t1 t2  in
                            if uu____86246
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____86259 = mk_eq2 wl env orig t1 t2  in
                               match uu____86259 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____86239 with
                          | (guard,wl1) ->
                              let uu____86280 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____86280))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____86283,FStar_Syntax_Syntax.Tm_let uu____86284) ->
                  let uu____86311 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____86311
                  then
                    let uu____86314 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____86314
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____86318,uu____86319) ->
                  let uu____86333 =
                    let uu____86339 =
                      let uu____86341 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____86343 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____86345 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____86347 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____86341 uu____86343 uu____86345 uu____86347
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____86339)
                     in
                  FStar_Errors.raise_error uu____86333
                    t1.FStar_Syntax_Syntax.pos
              | (uu____86351,FStar_Syntax_Syntax.Tm_let uu____86352) ->
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
              | uu____86384 -> giveup env "head tag mismatch" orig))))

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
          (let uu____86448 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____86448
           then
             let uu____86453 =
               let uu____86455 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____86455  in
             let uu____86456 =
               let uu____86458 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____86458  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____86453 uu____86456
           else ());
          (let uu____86462 =
             let uu____86464 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____86464  in
           if uu____86462
           then
             let uu____86467 =
               let uu____86469 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____86471 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____86469 uu____86471
                in
             giveup env uu____86467 orig
           else
             (let uu____86476 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____86476 with
              | (ret_sub_prob,wl1) ->
                  let uu____86484 =
                    FStar_List.fold_right2
                      (fun uu____86521  ->
                         fun uu____86522  ->
                           fun uu____86523  ->
                             match (uu____86521, uu____86522, uu____86523)
                             with
                             | ((a1,uu____86567),(a2,uu____86569),(arg_sub_probs,wl2))
                                 ->
                                 let uu____86602 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____86602 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____86484 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____86632 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____86632  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____86640 = attempt sub_probs wl3  in
                       solve env uu____86640)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____86663 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____86666)::[] -> wp1
              | uu____86691 ->
                  let uu____86702 =
                    let uu____86704 =
                      let uu____86706 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____86706  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____86704
                     in
                  failwith uu____86702
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____86713 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____86713]
              | x -> x  in
            let uu____86715 =
              let uu____86726 =
                let uu____86735 =
                  let uu____86736 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____86736 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____86735  in
              [uu____86726]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____86715;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____86754 = lift_c1 ()  in solve_eq uu____86754 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___616_86763  ->
                       match uu___616_86763 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____86768 -> false))
                in
             let uu____86770 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____86800)::uu____86801,(wp2,uu____86803)::uu____86804)
                   -> (wp1, wp2)
               | uu____86877 ->
                   let uu____86902 =
                     let uu____86908 =
                       let uu____86910 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____86912 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____86910 uu____86912
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____86908)
                      in
                   FStar_Errors.raise_error uu____86902
                     env.FStar_TypeChecker_Env.range
                in
             match uu____86770 with
             | (wpc1,wpc2) ->
                 let uu____86922 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____86922
                 then
                   let uu____86927 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____86927 wl
                 else
                   (let uu____86931 =
                      let uu____86938 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____86938  in
                    match uu____86931 with
                    | (c2_decl,qualifiers) ->
                        let uu____86959 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____86959
                        then
                          let c1_repr =
                            let uu____86966 =
                              let uu____86967 =
                                let uu____86968 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____86968  in
                              let uu____86969 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____86967 uu____86969
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____86966
                             in
                          let c2_repr =
                            let uu____86971 =
                              let uu____86972 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____86973 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____86972 uu____86973
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____86971
                             in
                          let uu____86974 =
                            let uu____86979 =
                              let uu____86981 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____86983 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____86981 uu____86983
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____86979
                             in
                          (match uu____86974 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____86989 = attempt [prob] wl2  in
                               solve env uu____86989)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____87004 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____87004
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____87013 =
                                     let uu____87020 =
                                       let uu____87021 =
                                         let uu____87038 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____87041 =
                                           let uu____87052 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____87061 =
                                             let uu____87072 =
                                               let uu____87081 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____87081
                                                in
                                             [uu____87072]  in
                                           uu____87052 :: uu____87061  in
                                         (uu____87038, uu____87041)  in
                                       FStar_Syntax_Syntax.Tm_app uu____87021
                                        in
                                     FStar_Syntax_Syntax.mk uu____87020  in
                                   uu____87013 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____87130 =
                                    let uu____87137 =
                                      let uu____87138 =
                                        let uu____87155 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____87158 =
                                          let uu____87169 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____87178 =
                                            let uu____87189 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____87198 =
                                              let uu____87209 =
                                                let uu____87218 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____87218
                                                 in
                                              [uu____87209]  in
                                            uu____87189 :: uu____87198  in
                                          uu____87169 :: uu____87178  in
                                        (uu____87155, uu____87158)  in
                                      FStar_Syntax_Syntax.Tm_app uu____87138
                                       in
                                    FStar_Syntax_Syntax.mk uu____87137  in
                                  uu____87130 FStar_Pervasives_Native.None r)
                              in
                           (let uu____87272 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____87272
                            then
                              let uu____87277 =
                                let uu____87279 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____87279
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____87277
                            else ());
                           (let uu____87283 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____87283 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____87292 =
                                    let uu____87295 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _87298  ->
                                         FStar_Pervasives_Native.Some _87298)
                                      uu____87295
                                     in
                                  solve_prob orig uu____87292 [] wl1  in
                                let uu____87299 = attempt [base_prob] wl2  in
                                solve env uu____87299))))
           in
        let uu____87300 = FStar_Util.physical_equality c1 c2  in
        if uu____87300
        then
          let uu____87303 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____87303
        else
          ((let uu____87307 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____87307
            then
              let uu____87312 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____87314 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____87312
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____87314
            else ());
           (let uu____87319 =
              let uu____87328 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____87331 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____87328, uu____87331)  in
            match uu____87319 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____87349),FStar_Syntax_Syntax.Total
                    (t2,uu____87351)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____87368 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____87368 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____87370,FStar_Syntax_Syntax.Total uu____87371) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____87390),FStar_Syntax_Syntax.Total
                    (t2,uu____87392)) ->
                     let uu____87409 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____87409 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____87412),FStar_Syntax_Syntax.GTotal
                    (t2,uu____87414)) ->
                     let uu____87431 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____87431 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____87434),FStar_Syntax_Syntax.GTotal
                    (t2,uu____87436)) ->
                     let uu____87453 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____87453 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____87455,FStar_Syntax_Syntax.Comp uu____87456) ->
                     let uu____87465 =
                       let uu___4158_87468 = problem  in
                       let uu____87471 =
                         let uu____87472 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____87472
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4158_87468.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____87471;
                         FStar_TypeChecker_Common.relation =
                           (uu___4158_87468.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___4158_87468.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___4158_87468.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4158_87468.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4158_87468.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4158_87468.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4158_87468.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4158_87468.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____87465 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____87473,FStar_Syntax_Syntax.Comp uu____87474) ->
                     let uu____87483 =
                       let uu___4158_87486 = problem  in
                       let uu____87489 =
                         let uu____87490 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____87490
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4158_87486.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____87489;
                         FStar_TypeChecker_Common.relation =
                           (uu___4158_87486.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___4158_87486.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___4158_87486.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4158_87486.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4158_87486.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4158_87486.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4158_87486.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4158_87486.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____87483 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____87491,FStar_Syntax_Syntax.GTotal uu____87492) ->
                     let uu____87501 =
                       let uu___4170_87504 = problem  in
                       let uu____87507 =
                         let uu____87508 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____87508
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4170_87504.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___4170_87504.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___4170_87504.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____87507;
                         FStar_TypeChecker_Common.element =
                           (uu___4170_87504.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4170_87504.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4170_87504.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4170_87504.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4170_87504.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4170_87504.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____87501 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____87509,FStar_Syntax_Syntax.Total uu____87510) ->
                     let uu____87519 =
                       let uu___4170_87522 = problem  in
                       let uu____87525 =
                         let uu____87526 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____87526
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4170_87522.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___4170_87522.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___4170_87522.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____87525;
                         FStar_TypeChecker_Common.element =
                           (uu___4170_87522.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4170_87522.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4170_87522.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4170_87522.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4170_87522.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4170_87522.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____87519 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____87527,FStar_Syntax_Syntax.Comp uu____87528) ->
                     let uu____87529 =
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
                     if uu____87529
                     then
                       let uu____87532 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____87532 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____87539 =
                            let uu____87544 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____87544
                            then (c1_comp, c2_comp)
                            else
                              (let uu____87553 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____87554 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____87553, uu____87554))
                             in
                          match uu____87539 with
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
                           (let uu____87562 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____87562
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____87570 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____87570 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____87573 =
                                  let uu____87575 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____87577 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____87575 uu____87577
                                   in
                                giveup env uu____87573 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____87588 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____87588 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____87638 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____87638 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____87663 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____87694  ->
                match uu____87694 with
                | (u1,u2) ->
                    let uu____87702 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____87704 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____87702 uu____87704))
         in
      FStar_All.pipe_right uu____87663 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____87741,[])) when
          let uu____87768 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____87768 -> "{}"
      | uu____87771 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____87798 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____87798
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____87810 =
              FStar_List.map
                (fun uu____87823  ->
                   match uu____87823 with
                   | (uu____87830,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____87810 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____87841 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____87841 imps
  
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
                  let uu____87898 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____87898
                  then
                    let uu____87906 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____87908 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____87906
                      (rel_to_string rel) uu____87908
                  else "TOP"  in
                let uu____87914 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____87914 with
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
              let uu____87974 =
                let uu____87977 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _87980  -> FStar_Pervasives_Native.Some _87980)
                  uu____87977
                 in
              FStar_Syntax_Syntax.new_bv uu____87974 t1  in
            let uu____87981 =
              let uu____87986 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____87986
               in
            match uu____87981 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____88046 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____88046
         then
           let uu____88051 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____88051
         else ());
        (let uu____88058 =
           FStar_Util.record_time (fun uu____88065  -> solve env probs)  in
         match uu____88058 with
         | (sol,ms) ->
             ((let uu____88077 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____88077
               then
                 let uu____88082 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____88082
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____88095 =
                     FStar_Util.record_time
                       (fun uu____88102  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____88095 with
                    | ((),ms1) ->
                        ((let uu____88113 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____88113
                          then
                            let uu____88118 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____88118
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____88132 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____88132
                     then
                       let uu____88139 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____88139
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
          ((let uu____88166 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____88166
            then
              let uu____88171 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____88171
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____88178 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____88178
             then
               let uu____88183 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____88183
             else ());
            (let f2 =
               let uu____88189 =
                 let uu____88190 = FStar_Syntax_Util.unmeta f1  in
                 uu____88190.FStar_Syntax_Syntax.n  in
               match uu____88189 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____88194 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___4286_88195 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___4286_88195.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___4286_88195.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___4286_88195.FStar_TypeChecker_Env.implicits)
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
            let uu____88250 =
              let uu____88251 =
                let uu____88252 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _88253  ->
                       FStar_TypeChecker_Common.NonTrivial _88253)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____88252;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____88251  in
            FStar_All.pipe_left
              (fun _88260  -> FStar_Pervasives_Native.Some _88260)
              uu____88250
  
let with_guard_no_simp :
  'Auu____88270 .
    'Auu____88270 ->
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
            let uu____88293 =
              let uu____88294 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _88295  -> FStar_TypeChecker_Common.NonTrivial _88295)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____88294;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____88293
  
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
          (let uu____88328 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____88328
           then
             let uu____88333 = FStar_Syntax_Print.term_to_string t1  in
             let uu____88335 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____88333
               uu____88335
           else ());
          (let uu____88340 =
             let uu____88345 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____88345
              in
           match uu____88340 with
           | (prob,wl) ->
               let g =
                 let uu____88353 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____88363  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____88353  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____88399 = try_teq true env t1 t2  in
        match uu____88399 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____88404 = FStar_TypeChecker_Env.get_range env  in
              let uu____88405 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____88404 uu____88405);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____88413 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____88413
              then
                let uu____88418 = FStar_Syntax_Print.term_to_string t1  in
                let uu____88420 = FStar_Syntax_Print.term_to_string t2  in
                let uu____88422 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____88418
                  uu____88420 uu____88422
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
          let uu____88448 = FStar_TypeChecker_Env.get_range env  in
          let uu____88449 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____88448 uu____88449
  
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
        (let uu____88478 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____88478
         then
           let uu____88483 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____88485 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____88483 uu____88485
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____88496 =
           let uu____88503 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____88503 "sub_comp"
            in
         match uu____88496 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____88516 =
                 FStar_Util.record_time
                   (fun uu____88528  ->
                      let uu____88529 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____88540  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____88529)
                  in
               match uu____88516 with
               | (r,ms) ->
                   ((let uu____88571 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____88571
                     then
                       let uu____88576 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____88578 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____88580 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____88576 uu____88578
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____88580
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
      fun uu____88618  ->
        match uu____88618 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____88661 =
                 let uu____88667 =
                   let uu____88669 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____88671 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____88669 uu____88671
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____88667)  in
               let uu____88675 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____88661 uu____88675)
               in
            let equiv1 v1 v' =
              let uu____88688 =
                let uu____88693 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____88694 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____88693, uu____88694)  in
              match uu____88688 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____88714 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____88745 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____88745 with
                      | FStar_Syntax_Syntax.U_unif uu____88752 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____88781  ->
                                    match uu____88781 with
                                    | (u,v') ->
                                        let uu____88790 = equiv1 v1 v'  in
                                        if uu____88790
                                        then
                                          let uu____88795 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____88795 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____88816 -> []))
               in
            let uu____88821 =
              let wl =
                let uu___4377_88825 = empty_worklist env  in
                {
                  attempting = (uu___4377_88825.attempting);
                  wl_deferred = (uu___4377_88825.wl_deferred);
                  ctr = (uu___4377_88825.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4377_88825.smt_ok);
                  umax_heuristic_ok = (uu___4377_88825.umax_heuristic_ok);
                  tcenv = (uu___4377_88825.tcenv);
                  wl_implicits = (uu___4377_88825.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____88844  ->
                      match uu____88844 with
                      | (lb,v1) ->
                          let uu____88851 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____88851 with
                           | USolved wl1 -> ()
                           | uu____88854 -> fail1 lb v1)))
               in
            let rec check_ineq uu____88865 =
              match uu____88865 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____88877) -> true
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
                      uu____88901,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____88903,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____88914) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____88922,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____88931 -> false)
               in
            let uu____88937 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____88954  ->
                      match uu____88954 with
                      | (u,v1) ->
                          let uu____88962 = check_ineq (u, v1)  in
                          if uu____88962
                          then true
                          else
                            ((let uu____88970 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____88970
                              then
                                let uu____88975 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____88977 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____88975
                                  uu____88977
                              else ());
                             false)))
               in
            if uu____88937
            then ()
            else
              ((let uu____88987 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____88987
                then
                  ((let uu____88993 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____88993);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____89005 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____89005))
                else ());
               (let uu____89018 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____89018))
  
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
        let fail1 uu____89092 =
          match uu____89092 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4454_89118 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___4454_89118.attempting);
            wl_deferred = (uu___4454_89118.wl_deferred);
            ctr = (uu___4454_89118.ctr);
            defer_ok;
            smt_ok = (uu___4454_89118.smt_ok);
            umax_heuristic_ok = (uu___4454_89118.umax_heuristic_ok);
            tcenv = (uu___4454_89118.tcenv);
            wl_implicits = (uu___4454_89118.wl_implicits)
          }  in
        (let uu____89121 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____89121
         then
           let uu____89126 = FStar_Util.string_of_bool defer_ok  in
           let uu____89128 = wl_to_string wl  in
           let uu____89130 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____89126 uu____89128 uu____89130
         else ());
        (let g1 =
           let uu____89136 = solve_and_commit env wl fail1  in
           match uu____89136 with
           | FStar_Pervasives_Native.Some
               (uu____89143::uu____89144,uu____89145) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4469_89174 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___4469_89174.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___4469_89174.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____89175 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___4474_89184 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4474_89184.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4474_89184.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___4474_89184.FStar_TypeChecker_Env.implicits)
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
    let uu____89227 = FStar_ST.op_Bang last_proof_ns  in
    match uu____89227 with
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
            let uu___4493_89352 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___4493_89352.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___4493_89352.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___4493_89352.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____89353 =
            let uu____89355 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____89355  in
          if uu____89353
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____89367 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____89368 =
                       let uu____89370 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____89370
                        in
                     FStar_Errors.diag uu____89367 uu____89368)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____89378 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____89379 =
                        let uu____89381 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____89381
                         in
                      FStar_Errors.diag uu____89378 uu____89379)
                   else ();
                   (let uu____89387 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____89387
                      "discharge_guard'" env vc1);
                   (let uu____89389 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____89389 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____89398 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____89399 =
                                let uu____89401 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____89401
                                 in
                              FStar_Errors.diag uu____89398 uu____89399)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____89411 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____89412 =
                                let uu____89414 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____89414
                                 in
                              FStar_Errors.diag uu____89411 uu____89412)
                           else ();
                           (let vcs =
                              let uu____89428 = FStar_Options.use_tactics ()
                                 in
                              if uu____89428
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____89450  ->
                                     (let uu____89452 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____89452);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____89496  ->
                                              match uu____89496 with
                                              | (env1,goal,opts) ->
                                                  let uu____89512 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____89512, opts)))))
                              else
                                (let uu____89515 =
                                   let uu____89522 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____89522)  in
                                 [uu____89515])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____89555  ->
                                    match uu____89555 with
                                    | (env1,goal,opts) ->
                                        let uu____89565 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____89565 with
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
                                                (let uu____89577 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____89578 =
                                                   let uu____89580 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____89582 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____89580 uu____89582
                                                    in
                                                 FStar_Errors.diag
                                                   uu____89577 uu____89578)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____89589 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____89590 =
                                                   let uu____89592 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____89592
                                                    in
                                                 FStar_Errors.diag
                                                   uu____89589 uu____89590)
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
      let uu____89610 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____89610 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____89619 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____89619
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____89633 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____89633 with
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
        let uu____89663 = try_teq false env t1 t2  in
        match uu____89663 with
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
            let uu____89707 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____89707 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____89720 ->
                     let uu____89733 =
                       let uu____89734 = FStar_Syntax_Subst.compress r  in
                       uu____89734.FStar_Syntax_Syntax.n  in
                     (match uu____89733 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____89739) ->
                          unresolved ctx_u'
                      | uu____89756 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____89780 = acc  in
            match uu____89780 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____89799 = hd1  in
                     (match uu____89799 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____89810 = unresolved ctx_u  in
                             if uu____89810
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____89834 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____89834
                                     then
                                       let uu____89838 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____89838
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____89847 = teq_nosmt env1 t tm
                                          in
                                       match uu____89847 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Env.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4606_89857 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4606_89857.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4606_89857.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4606_89857.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4606_89857.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4606_89857.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4606_89857.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4606_89857.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4609_89865 = hd1  in
                                       {
                                         FStar_TypeChecker_Env.imp_reason =
                                           (uu___4609_89865.FStar_TypeChecker_Env.imp_reason);
                                         FStar_TypeChecker_Env.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Env.imp_tm =
                                           (uu___4609_89865.FStar_TypeChecker_Env.imp_tm);
                                         FStar_TypeChecker_Env.imp_range =
                                           (uu___4609_89865.FStar_TypeChecker_Env.imp_range)
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
                                    let uu___4613_89876 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4613_89876.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4613_89876.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4613_89876.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4613_89876.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4613_89876.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4613_89876.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4613_89876.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4613_89876.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4613_89876.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___4613_89876.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4613_89876.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4613_89876.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4613_89876.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4613_89876.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4613_89876.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4613_89876.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4613_89876.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4613_89876.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4613_89876.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4613_89876.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4613_89876.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4613_89876.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4613_89876.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4613_89876.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4613_89876.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4613_89876.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4613_89876.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4613_89876.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4613_89876.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4613_89876.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4613_89876.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4613_89876.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4613_89876.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4613_89876.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4613_89876.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4613_89876.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4613_89876.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4613_89876.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4613_89876.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4613_89876.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4613_89876.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4613_89876.FStar_TypeChecker_Env.nbe)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4618_89880 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4618_89880.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4618_89880.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4618_89880.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4618_89880.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4618_89880.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4618_89880.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4618_89880.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4618_89880.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4618_89880.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4618_89880.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___4618_89880.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4618_89880.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4618_89880.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4618_89880.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4618_89880.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4618_89880.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4618_89880.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4618_89880.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4618_89880.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4618_89880.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4618_89880.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4618_89880.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4618_89880.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4618_89880.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4618_89880.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4618_89880.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4618_89880.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4618_89880.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4618_89880.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4618_89880.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4618_89880.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4618_89880.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4618_89880.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4618_89880.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4618_89880.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4618_89880.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4618_89880.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4618_89880.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4618_89880.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4618_89880.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4618_89880.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4618_89880.FStar_TypeChecker_Env.nbe)
                                      }
                                    else env1  in
                                  (let uu____89885 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____89885
                                   then
                                     let uu____89890 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____89892 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____89894 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____89896 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____89890 uu____89892 uu____89894
                                       reason uu____89896
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4624_89903  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____89910 =
                                             let uu____89920 =
                                               let uu____89928 =
                                                 let uu____89930 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____89932 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____89934 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____89930 uu____89932
                                                   uu____89934
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____89928, r)
                                                in
                                             [uu____89920]  in
                                           FStar_Errors.add_errors
                                             uu____89910);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___4632_89954 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___4632_89954.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___4632_89954.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___4632_89954.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____89958 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____89969  ->
                                               let uu____89970 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____89972 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____89974 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____89970 uu____89972
                                                 reason uu____89974)) env2 g2
                                         true
                                        in
                                     match uu____89958 with
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
          let uu___4640_89982 = g  in
          let uu____89983 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4640_89982.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4640_89982.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___4640_89982.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____89983
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
        let uu____90026 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____90026 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____90027 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____90027
      | imp::uu____90029 ->
          let uu____90032 =
            let uu____90038 =
              let uu____90040 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____90042 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____90040 uu____90042 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____90038)
             in
          FStar_Errors.raise_error uu____90032
            imp.FStar_TypeChecker_Env.imp_range
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____90064 = teq_nosmt env t1 t2  in
        match uu____90064 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4662_90083 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___4662_90083.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___4662_90083.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___4662_90083.FStar_TypeChecker_Env.implicits)
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
        (let uu____90119 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____90119
         then
           let uu____90124 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____90126 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____90124
             uu____90126
         else ());
        (let uu____90131 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____90131 with
         | (prob,x,wl) ->
             let g =
               let uu____90150 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____90161  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____90150  in
             ((let uu____90182 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____90182
               then
                 let uu____90187 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____90189 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____90191 =
                   let uu____90193 = FStar_Util.must g  in
                   guard_to_string env uu____90193  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____90187 uu____90189 uu____90191
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
        let uu____90230 = check_subtyping env t1 t2  in
        match uu____90230 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____90249 =
              let uu____90250 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____90250 g  in
            FStar_Pervasives_Native.Some uu____90249
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____90269 = check_subtyping env t1 t2  in
        match uu____90269 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____90288 =
              let uu____90289 =
                let uu____90290 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____90290]  in
              FStar_TypeChecker_Env.close_guard env uu____90289 g  in
            FStar_Pervasives_Native.Some uu____90288
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____90328 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____90328
         then
           let uu____90333 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____90335 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____90333
             uu____90335
         else ());
        (let uu____90340 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____90340 with
         | (prob,x,wl) ->
             let g =
               let uu____90355 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____90366  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____90355  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____90390 =
                      let uu____90391 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____90391]  in
                    FStar_TypeChecker_Env.close_guard env uu____90390 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____90432 = subtype_nosmt env t1 t2  in
        match uu____90432 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  