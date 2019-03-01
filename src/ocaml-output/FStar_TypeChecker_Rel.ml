open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____65127 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____65163 -> false
  
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
                    let uu____65587 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____65587;
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
                     (let uu___656_65619 = wl  in
                      {
                        attempting = (uu___656_65619.attempting);
                        wl_deferred = (uu___656_65619.wl_deferred);
                        ctr = (uu___656_65619.ctr);
                        defer_ok = (uu___656_65619.defer_ok);
                        smt_ok = (uu___656_65619.smt_ok);
                        umax_heuristic_ok =
                          (uu___656_65619.umax_heuristic_ok);
                        tcenv = (uu___656_65619.tcenv);
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
            let uu___662_65652 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___662_65652.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___662_65652.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___662_65652.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___662_65652.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___662_65652.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___662_65652.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___662_65652.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___662_65652.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___662_65652.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___662_65652.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___662_65652.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___662_65652.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___662_65652.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___662_65652.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___662_65652.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___662_65652.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___662_65652.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___662_65652.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___662_65652.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___662_65652.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___662_65652.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___662_65652.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___662_65652.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___662_65652.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___662_65652.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___662_65652.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___662_65652.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___662_65652.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___662_65652.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___662_65652.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___662_65652.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___662_65652.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___662_65652.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___662_65652.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___662_65652.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___662_65652.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___662_65652.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___662_65652.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___662_65652.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___662_65652.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___662_65652.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___662_65652.FStar_TypeChecker_Env.nbe)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____65654 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____65654 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Env.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * Prims.string) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____65697 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____65734 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * Prims.string)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____65768 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____65779 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____65790 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___585_65808  ->
    match uu___585_65808 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____65820 = FStar_Syntax_Util.head_and_args t  in
    match uu____65820 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____65883 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____65885 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____65900 =
                     let uu____65902 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____65902  in
                   FStar_Util.format1 "@<%s>" uu____65900
                in
             let uu____65906 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____65883 uu____65885 uu____65906
         | uu____65909 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___586_65921  ->
      match uu___586_65921 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____65926 =
            let uu____65930 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____65932 =
              let uu____65936 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____65938 =
                let uu____65942 =
                  let uu____65946 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____65946]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____65942
                 in
              uu____65936 :: uu____65938  in
            uu____65930 :: uu____65932  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____65926
      | FStar_TypeChecker_Common.CProb p ->
          let uu____65957 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____65959 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____65961 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____65957
            uu____65959 (rel_to_string p.FStar_TypeChecker_Common.relation)
            uu____65961
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___587_65975  ->
      match uu___587_65975 with
      | UNIV (u,t) ->
          let x =
            let uu____65981 = FStar_Options.hide_uvar_nums ()  in
            if uu____65981
            then "?"
            else
              (let uu____65988 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____65988 FStar_Util.string_of_int)
             in
          let uu____65992 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____65992
      | TERM (u,t) ->
          let x =
            let uu____65999 = FStar_Options.hide_uvar_nums ()  in
            if uu____65999
            then "?"
            else
              (let uu____66006 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____66006 FStar_Util.string_of_int)
             in
          let uu____66010 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____66010
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____66029 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____66029 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____66050 =
      let uu____66054 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____66054
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____66050 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____66073 .
    (FStar_Syntax_Syntax.term * 'Auu____66073) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____66092 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____66113  ->
              match uu____66113 with
              | (x,uu____66120) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____66092 (FStar_String.concat " ")
  
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
        (let uu____66163 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____66163
         then
           let uu____66168 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____66168
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___588_66179  ->
    match uu___588_66179 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____66185 .
    'Auu____66185 FStar_TypeChecker_Common.problem ->
      'Auu____66185 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___722_66197 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___722_66197.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___722_66197.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___722_66197.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___722_66197.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___722_66197.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___722_66197.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___722_66197.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____66205 .
    'Auu____66205 FStar_TypeChecker_Common.problem ->
      'Auu____66205 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___589_66225  ->
    match uu___589_66225 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _66231  -> FStar_TypeChecker_Common.TProb _66231)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _66237  -> FStar_TypeChecker_Common.CProb _66237)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___590_66243  ->
    match uu___590_66243 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___734_66249 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___734_66249.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___734_66249.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___734_66249.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___734_66249.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___734_66249.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___734_66249.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___734_66249.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___734_66249.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___734_66249.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___738_66257 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___738_66257.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___738_66257.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___738_66257.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___738_66257.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___738_66257.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___738_66257.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___738_66257.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___738_66257.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___738_66257.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___591_66270  ->
      match uu___591_66270 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___592_66277  ->
    match uu___592_66277 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___593_66290  ->
    match uu___593_66290 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___594_66305  ->
    match uu___594_66305 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___595_66320  ->
    match uu___595_66320 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___596_66334  ->
    match uu___596_66334 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___597_66348  ->
    match uu___597_66348 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___598_66360  ->
    match uu___598_66360 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____66376 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____66376) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____66406 =
          let uu____66408 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____66408  in
        if uu____66406
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____66445)::bs ->
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
          let uu____66492 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____66516 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____66516]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____66492
      | FStar_TypeChecker_Common.CProb p ->
          let uu____66544 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____66568 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____66568]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____66544
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____66615 =
          let uu____66617 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____66617  in
        if uu____66615
        then ()
        else
          (let uu____66622 =
             let uu____66625 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____66625
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____66622 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____66674 =
          let uu____66676 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____66676  in
        if uu____66674
        then ()
        else
          (let uu____66681 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____66681)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____66701 =
        let uu____66703 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____66703  in
      if uu____66701
      then ()
      else
        (let msgf m =
           let uu____66717 =
             let uu____66719 =
               let uu____66721 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____66721 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____66719  in
           Prims.op_Hat msg uu____66717  in
         (let uu____66726 = msgf "scope"  in
          let uu____66729 = p_scope prob  in
          def_scope_wf uu____66726 (p_loc prob) uu____66729);
         (let uu____66741 = msgf "guard"  in
          def_check_scoped uu____66741 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____66748 = msgf "lhs"  in
                def_check_scoped uu____66748 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____66751 = msgf "rhs"  in
                def_check_scoped uu____66751 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____66758 = msgf "lhs"  in
                def_check_scoped_comp uu____66758 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____66761 = msgf "rhs"  in
                def_check_scoped_comp uu____66761 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___831_66782 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___831_66782.wl_deferred);
          ctr = (uu___831_66782.ctr);
          defer_ok = (uu___831_66782.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___831_66782.umax_heuristic_ok);
          tcenv = (uu___831_66782.tcenv);
          wl_implicits = (uu___831_66782.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____66790 .
    FStar_TypeChecker_Env.env ->
      ('Auu____66790 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___835_66813 = empty_worklist env  in
      let uu____66814 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____66814;
        wl_deferred = (uu___835_66813.wl_deferred);
        ctr = (uu___835_66813.ctr);
        defer_ok = (uu___835_66813.defer_ok);
        smt_ok = (uu___835_66813.smt_ok);
        umax_heuristic_ok = (uu___835_66813.umax_heuristic_ok);
        tcenv = (uu___835_66813.tcenv);
        wl_implicits = (uu___835_66813.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___840_66837 = wl  in
        {
          attempting = (uu___840_66837.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___840_66837.ctr);
          defer_ok = (uu___840_66837.defer_ok);
          smt_ok = (uu___840_66837.smt_ok);
          umax_heuristic_ok = (uu___840_66837.umax_heuristic_ok);
          tcenv = (uu___840_66837.tcenv);
          wl_implicits = (uu___840_66837.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___845_66865 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___845_66865.wl_deferred);
         ctr = (uu___845_66865.ctr);
         defer_ok = (uu___845_66865.defer_ok);
         smt_ok = (uu___845_66865.smt_ok);
         umax_heuristic_ok = (uu___845_66865.umax_heuristic_ok);
         tcenv = (uu___845_66865.tcenv);
         wl_implicits = (uu___845_66865.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____66879 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____66879 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____66913 = FStar_Syntax_Util.type_u ()  in
            match uu____66913 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____66925 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____66925 with
                 | (uu____66943,tt,wl1) ->
                     let uu____66946 = FStar_Syntax_Util.mk_eq2 u tt t1 t2
                        in
                     (uu____66946, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___599_66952  ->
    match uu___599_66952 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _66958  -> FStar_TypeChecker_Common.TProb _66958) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _66964  -> FStar_TypeChecker_Common.CProb _66964) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____66972 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____66972 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____66992  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____67089 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____67089 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____67089 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____67089 FStar_TypeChecker_Common.problem *
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
                        let uu____67176 =
                          let uu____67185 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____67185]  in
                        FStar_List.append scope uu____67176
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____67228 =
                      let uu____67231 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____67231  in
                    FStar_List.append uu____67228
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____67250 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____67250 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____67276 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____67276;
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
                  (let uu____67350 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____67350 with
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
                  (let uu____67438 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____67438 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____67476 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____67476 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____67476 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____67476 FStar_TypeChecker_Common.problem *
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
                          let uu____67544 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____67544]  in
                        let uu____67563 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____67563
                     in
                  let uu____67566 =
                    let uu____67573 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___928_67584 = wl  in
                       {
                         attempting = (uu___928_67584.attempting);
                         wl_deferred = (uu___928_67584.wl_deferred);
                         ctr = (uu___928_67584.ctr);
                         defer_ok = (uu___928_67584.defer_ok);
                         smt_ok = (uu___928_67584.smt_ok);
                         umax_heuristic_ok =
                           (uu___928_67584.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___928_67584.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____67573
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____67566 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____67602 =
                              let uu____67607 =
                                let uu____67608 =
                                  let uu____67617 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____67617
                                   in
                                [uu____67608]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____67607
                               in
                            uu____67602 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____67647 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____67647;
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
                let uu____67695 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____67695;
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
  'Auu____67710 .
    worklist ->
      'Auu____67710 FStar_TypeChecker_Common.problem ->
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
              let uu____67743 =
                let uu____67746 =
                  let uu____67747 =
                    let uu____67754 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____67754)  in
                  FStar_Syntax_Syntax.NT uu____67747  in
                [uu____67746]  in
              FStar_Syntax_Subst.subst uu____67743 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____67778 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____67778
        then
          let uu____67786 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____67789 = prob_to_string env d  in
          let uu____67791 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____67786 uu____67789 uu____67791 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____67807 -> failwith "impossible"  in
           let uu____67810 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____67826 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____67828 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____67826, uu____67828)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____67835 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____67837 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____67835, uu____67837)
              in
           match uu____67810 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___600_67865  ->
            match uu___600_67865 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____67877 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____67881 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____67881 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___601_67912  ->
           match uu___601_67912 with
           | UNIV uu____67915 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____67922 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____67922
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
        (fun uu___602_67950  ->
           match uu___602_67950 with
           | UNIV (u',t) ->
               let uu____67955 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____67955
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____67962 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____67974 =
        let uu____67975 =
          let uu____67976 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____67976
           in
        FStar_Syntax_Subst.compress uu____67975  in
      FStar_All.pipe_right uu____67974 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____67988 =
        let uu____67989 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____67989  in
      FStar_All.pipe_right uu____67988 FStar_Syntax_Util.unlazy_emb
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____67997 = FStar_Syntax_Util.head_and_args t  in
    match uu____67997 with
    | (h,uu____68016) ->
        let uu____68041 =
          let uu____68042 = FStar_Syntax_Subst.compress h  in
          uu____68042.FStar_Syntax_Syntax.n  in
        (match uu____68041 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____68047 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____68060 = should_strongly_reduce t  in
      if uu____68060
      then
        let uu____68063 =
          let uu____68064 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Reify;
              FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant] env t
             in
          FStar_Syntax_Subst.compress uu____68064  in
        FStar_All.pipe_right uu____68063 FStar_Syntax_Util.unlazy_emb
      else whnf' env t
  
let norm_arg :
  'Auu____68074 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____68074) ->
        (FStar_Syntax_Syntax.term * 'Auu____68074)
  =
  fun env  ->
    fun t  ->
      let uu____68097 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____68097, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____68149  ->
              match uu____68149 with
              | (x,imp) ->
                  let uu____68168 =
                    let uu___1025_68169 = x  in
                    let uu____68170 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1025_68169.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1025_68169.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____68170
                    }  in
                  (uu____68168, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____68194 = aux u3  in
            FStar_Syntax_Syntax.U_succ uu____68194
        | FStar_Syntax_Syntax.U_max us ->
            let uu____68198 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____68198
        | uu____68201 -> u2  in
      let uu____68202 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____68202
  
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
                (let uu____68323 = norm_refinement env t12  in
                 match uu____68323 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____68338;
                     FStar_Syntax_Syntax.vars = uu____68339;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____68363 =
                       let uu____68365 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____68367 = FStar_Syntax_Print.tag_of_term tt
                          in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____68365 uu____68367
                        in
                     failwith uu____68363)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____68383 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____68383
          | FStar_Syntax_Syntax.Tm_uinst uu____68384 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____68421 =
                   let uu____68422 = FStar_Syntax_Subst.compress t1'  in
                   uu____68422.FStar_Syntax_Syntax.n  in
                 match uu____68421 with
                 | FStar_Syntax_Syntax.Tm_refine uu____68437 -> aux true t1'
                 | uu____68445 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____68460 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____68491 =
                   let uu____68492 = FStar_Syntax_Subst.compress t1'  in
                   uu____68492.FStar_Syntax_Syntax.n  in
                 match uu____68491 with
                 | FStar_Syntax_Syntax.Tm_refine uu____68507 -> aux true t1'
                 | uu____68515 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____68530 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____68577 =
                   let uu____68578 = FStar_Syntax_Subst.compress t1'  in
                   uu____68578.FStar_Syntax_Syntax.n  in
                 match uu____68577 with
                 | FStar_Syntax_Syntax.Tm_refine uu____68593 -> aux true t1'
                 | uu____68601 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____68616 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____68631 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____68646 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____68661 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____68676 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____68705 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____68738 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____68759 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____68786 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____68814 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____68851 ->
              let uu____68858 =
                let uu____68860 = FStar_Syntax_Print.term_to_string t12  in
                let uu____68862 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____68860 uu____68862
                 in
              failwith uu____68858
          | FStar_Syntax_Syntax.Tm_ascribed uu____68877 ->
              let uu____68904 =
                let uu____68906 = FStar_Syntax_Print.term_to_string t12  in
                let uu____68908 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____68906 uu____68908
                 in
              failwith uu____68904
          | FStar_Syntax_Syntax.Tm_delayed uu____68923 ->
              let uu____68946 =
                let uu____68948 = FStar_Syntax_Print.term_to_string t12  in
                let uu____68950 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____68948 uu____68950
                 in
              failwith uu____68946
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____68965 =
                let uu____68967 = FStar_Syntax_Print.term_to_string t12  in
                let uu____68969 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____68967 uu____68969
                 in
              failwith uu____68965
           in
        let uu____68984 = whnf env t1  in aux false uu____68984
  
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
      let uu____69045 = base_and_refinement env t  in
      FStar_All.pipe_right uu____69045 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____69086 = FStar_Syntax_Syntax.null_bv t  in
    (uu____69086, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____69113 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____69113 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____69173  ->
    match uu____69173 with
    | (t_base,refopt) ->
        let uu____69204 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____69204 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____69246 =
      let uu____69250 =
        let uu____69253 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____69280  ->
                  match uu____69280 with | (uu____69289,uu____69290,x) -> x))
           in
        FStar_List.append wl.attempting uu____69253  in
      FStar_List.map (wl_prob_to_string wl) uu____69250  in
    FStar_All.pipe_right uu____69246 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____69313 .
    ('Auu____69313 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____69325  ->
    match uu____69325 with
    | (uu____69332,c,args) ->
        let uu____69335 = print_ctx_uvar c  in
        let uu____69337 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____69335 uu____69337
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____69347 = FStar_Syntax_Util.head_and_args t  in
    match uu____69347 with
    | (head1,_args) ->
        let uu____69391 =
          let uu____69392 = FStar_Syntax_Subst.compress head1  in
          uu____69392.FStar_Syntax_Syntax.n  in
        (match uu____69391 with
         | FStar_Syntax_Syntax.Tm_uvar uu____69396 -> true
         | uu____69410 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____69418 = FStar_Syntax_Util.head_and_args t  in
    match uu____69418 with
    | (head1,_args) ->
        let uu____69461 =
          let uu____69462 = FStar_Syntax_Subst.compress head1  in
          uu____69462.FStar_Syntax_Syntax.n  in
        (match uu____69461 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____69466) -> u
         | uu____69483 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____69508 = FStar_Syntax_Util.head_and_args t  in
      match uu____69508 with
      | (head1,args) ->
          let uu____69555 =
            let uu____69556 = FStar_Syntax_Subst.compress head1  in
            uu____69556.FStar_Syntax_Syntax.n  in
          (match uu____69555 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____69564)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____69597 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___603_69622  ->
                         match uu___603_69622 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____69627 =
                               let uu____69628 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____69628.FStar_Syntax_Syntax.n  in
                             (match uu____69627 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____69633 -> false)
                         | uu____69635 -> true))
                  in
               (match uu____69597 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____69660 =
                        FStar_List.collect
                          (fun uu___604_69672  ->
                             match uu___604_69672 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____69676 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____69676]
                             | uu____69677 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____69660 FStar_List.rev  in
                    let uu____69700 =
                      let uu____69707 =
                        let uu____69716 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___605_69738  ->
                                  match uu___605_69738 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____69742 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____69742]
                                  | uu____69743 -> []))
                           in
                        FStar_All.pipe_right uu____69716 FStar_List.rev  in
                      let uu____69766 =
                        let uu____69769 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____69769  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____69707 uu____69766
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____69700 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____69805  ->
                                match uu____69805 with
                                | (x,i) ->
                                    let uu____69824 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____69824, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____69855  ->
                                match uu____69855 with
                                | (a,i) ->
                                    let uu____69874 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____69874, i)) args_sol
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
           | uu____69896 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____69918 =
          let uu____69941 =
            let uu____69942 = FStar_Syntax_Subst.compress k  in
            uu____69942.FStar_Syntax_Syntax.n  in
          match uu____69941 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____70024 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____70024)
              else
                (let uu____70059 = FStar_Syntax_Util.abs_formals t  in
                 match uu____70059 with
                 | (ys',t1,uu____70092) ->
                     let uu____70097 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____70097))
          | uu____70136 ->
              let uu____70137 =
                let uu____70142 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____70142)  in
              ((ys, t), uu____70137)
           in
        match uu____69918 with
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
                 let uu____70237 = FStar_Syntax_Util.rename_binders xs ys1
                    in
                 FStar_Syntax_Subst.subst_comp uu____70237 c  in
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
               (let uu____70315 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____70315
                then
                  let uu____70320 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____70322 = print_ctx_uvar uv  in
                  let uu____70324 = FStar_Syntax_Print.term_to_string phi1
                     in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____70320 uu____70322 uu____70324
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____70333 =
                   let uu____70335 = FStar_Util.string_of_int (p_pid prob)
                      in
                   Prims.op_Hat "solve_prob'.sol." uu____70335  in
                 let uu____70338 =
                   let uu____70341 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____70341
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____70333 uu____70338 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____70374 =
               let uu____70375 =
                 let uu____70377 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____70379 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____70377 uu____70379
                  in
               failwith uu____70375  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____70445  ->
                       match uu____70445 with
                       | (a,i) ->
                           let uu____70466 =
                             let uu____70467 = FStar_Syntax_Subst.compress a
                                in
                             uu____70467.FStar_Syntax_Syntax.n  in
                           (match uu____70466 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____70493 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____70503 =
                 let uu____70505 = is_flex g  in
                 Prims.op_Negation uu____70505  in
               if uu____70503
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____70514 = destruct_flex_t g wl  in
                  match uu____70514 with
                  | ((uu____70519,uv1,args),wl1) ->
                      ((let uu____70524 = args_as_binders args  in
                        assign_solution uu____70524 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___1277_70526 = wl1  in
              {
                attempting = (uu___1277_70526.attempting);
                wl_deferred = (uu___1277_70526.wl_deferred);
                ctr = (wl1.ctr + (Prims.parse_int "1"));
                defer_ok = (uu___1277_70526.defer_ok);
                smt_ok = (uu___1277_70526.smt_ok);
                umax_heuristic_ok = (uu___1277_70526.umax_heuristic_ok);
                tcenv = (uu___1277_70526.tcenv);
                wl_implicits = (uu___1277_70526.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____70551 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____70551
         then
           let uu____70556 = FStar_Util.string_of_int pid  in
           let uu____70558 =
             let uu____70560 = FStar_List.map (uvi_to_string wl.tcenv) sol
                in
             FStar_All.pipe_right uu____70560 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____70556
             uu____70558
         else ());
        commit sol;
        (let uu___1285_70574 = wl  in
         {
           attempting = (uu___1285_70574.attempting);
           wl_deferred = (uu___1285_70574.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___1285_70574.defer_ok);
           smt_ok = (uu___1285_70574.smt_ok);
           umax_heuristic_ok = (uu___1285_70574.umax_heuristic_ok);
           tcenv = (uu___1285_70574.tcenv);
           wl_implicits = (uu___1285_70574.wl_implicits)
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
             | (uu____70640,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____70668 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____70668
              in
           (let uu____70674 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____70674
            then
              let uu____70679 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____70683 =
                let uu____70685 =
                  FStar_List.map (uvi_to_string wl.tcenv) uvis  in
                FStar_All.pipe_right uu____70685 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____70679
                uu____70683
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
        let uu____70720 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____70720 FStar_Util.set_elements  in
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
      let uu____70760 = occurs uk t  in
      match uu____70760 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____70799 =
                 let uu____70801 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____70803 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____70801 uu____70803
                  in
               FStar_Pervasives_Native.Some uu____70799)
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
            let uu____70923 = maximal_prefix bs_tail bs'_tail  in
            (match uu____70923 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____70974 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____71031  ->
             match uu____71031 with
             | (x,uu____71043) -> (FStar_Syntax_Syntax.Binding_var x) :: g1)
        g bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____71061 = FStar_List.last bs  in
      match uu____71061 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____71085) ->
          let uu____71096 =
            FStar_Util.prefix_until
              (fun uu___606_71111  ->
                 match uu___606_71111 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____71114 -> false) g
             in
          (match uu____71096 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____71128,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____71165 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____71165 with
        | (pfx,uu____71175) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____71187 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____71187 with
             | (uu____71195,src',wl1) ->
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
                 | uu____71309 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____71310 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____71374  ->
                  fun uu____71375  ->
                    match (uu____71374, uu____71375) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____71478 =
                          let uu____71480 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____71480
                           in
                        if uu____71478
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____71514 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____71514
                           then
                             let uu____71531 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____71531)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____71310 with | (isect,uu____71581) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____71617 'Auu____71618 .
    (FStar_Syntax_Syntax.bv * 'Auu____71617) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____71618) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____71676  ->
              fun uu____71677  ->
                match (uu____71676, uu____71677) with
                | ((a,uu____71696),(b,uu____71698)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____71714 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____71714) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____71745  ->
           match uu____71745 with
           | (y,uu____71752) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____71762 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____71762) Prims.list ->
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
                   let uu____71924 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____71924
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____71957 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____72009 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____72054 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____72076 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___607_72084  ->
    match uu___607_72084 with
    | MisMatch (d1,d2) ->
        let uu____72096 =
          let uu____72098 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____72100 =
            let uu____72102 =
              let uu____72104 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____72104 ")"  in
            Prims.op_Hat ") (" uu____72102  in
          Prims.op_Hat uu____72098 uu____72100  in
        Prims.op_Hat "MisMatch (" uu____72096
    | HeadMatch u ->
        let uu____72111 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____72111
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___608_72120  ->
    match uu___608_72120 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____72137 -> HeadMatch false
  
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
          let uu____72159 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____72159 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____72170 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____72194 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____72204 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____72231 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____72231
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____72232 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____72233 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____72234 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____72247 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____72261 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____72285) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____72291,uu____72292) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____72334) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____72359;
             FStar_Syntax_Syntax.index = uu____72360;
             FStar_Syntax_Syntax.sort = t2;_},uu____72362)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____72370 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____72371 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____72372 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____72387 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____72394 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____72414 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____72414
  
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
           { FStar_Syntax_Syntax.blob = uu____72433;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____72434;
             FStar_Syntax_Syntax.ltyp = uu____72435;
             FStar_Syntax_Syntax.rng = uu____72436;_},uu____72437)
            ->
            let uu____72448 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____72448 t21
        | (uu____72449,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____72450;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____72451;
             FStar_Syntax_Syntax.ltyp = uu____72452;
             FStar_Syntax_Syntax.rng = uu____72453;_})
            ->
            let uu____72464 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____72464
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____72476 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____72476
            then FullMatch
            else
              (let uu____72481 =
                 let uu____72490 =
                   let uu____72493 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____72493  in
                 let uu____72494 =
                   let uu____72497 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____72497  in
                 (uu____72490, uu____72494)  in
               MisMatch uu____72481)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____72503),FStar_Syntax_Syntax.Tm_uinst (g,uu____72505)) ->
            let uu____72514 = head_matches env f g  in
            FStar_All.pipe_right uu____72514 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____72515) -> HeadMatch true
        | (uu____72517,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____72521 = FStar_Const.eq_const c d  in
            if uu____72521
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____72531),FStar_Syntax_Syntax.Tm_uvar (uv',uu____72533)) ->
            let uu____72566 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____72566
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____72576),FStar_Syntax_Syntax.Tm_refine (y,uu____72578)) ->
            let uu____72587 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____72587 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____72589),uu____72590) ->
            let uu____72595 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____72595 head_match
        | (uu____72596,FStar_Syntax_Syntax.Tm_refine (x,uu____72598)) ->
            let uu____72603 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____72603 head_match
        | (FStar_Syntax_Syntax.Tm_type
           uu____72604,FStar_Syntax_Syntax.Tm_type uu____72605) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____72607,FStar_Syntax_Syntax.Tm_arrow uu____72608) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____72639),FStar_Syntax_Syntax.Tm_app
           (head',uu____72641)) ->
            let uu____72690 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____72690 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____72692),uu____72693) ->
            let uu____72718 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____72718 head_match
        | (uu____72719,FStar_Syntax_Syntax.Tm_app (head1,uu____72721)) ->
            let uu____72746 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____72746 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____72747,FStar_Syntax_Syntax.Tm_let
           uu____72748) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____72776,FStar_Syntax_Syntax.Tm_match uu____72777) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____72823,FStar_Syntax_Syntax.Tm_abs
           uu____72824) -> HeadMatch true
        | uu____72862 ->
            let uu____72867 =
              let uu____72876 = delta_depth_of_term env t11  in
              let uu____72879 = delta_depth_of_term env t21  in
              (uu____72876, uu____72879)  in
            MisMatch uu____72867
  
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
            (let uu____72945 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____72945
             then
               let uu____72950 = FStar_Syntax_Print.term_to_string t  in
               let uu____72952 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____72950 uu____72952
             else ());
            (let uu____72957 =
               let uu____72958 = FStar_Syntax_Util.un_uinst head1  in
               uu____72958.FStar_Syntax_Syntax.n  in
             match uu____72957 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____72964 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____72964 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____72978 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____72978
                        then
                          let uu____72983 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____72983
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____72988 ->
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
                      let uu____73005 =
                        let uu____73007 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____73007 = FStar_Syntax_Util.Equal  in
                      if uu____73005
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____73014 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____73014
                          then
                            let uu____73019 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____73021 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n"
                              uu____73019 uu____73021
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____73026 -> FStar_Pervasives_Native.None)
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
            (let uu____73178 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____73178
             then
               let uu____73183 = FStar_Syntax_Print.term_to_string t11  in
               let uu____73185 = FStar_Syntax_Print.term_to_string t21  in
               let uu____73187 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____73183
                 uu____73185 uu____73187
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____73215 =
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
               match uu____73215 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____73263 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____73263 with
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
                  uu____73301),uu____73302)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____73323 =
                      let uu____73332 = maybe_inline t11  in
                      let uu____73335 = maybe_inline t21  in
                      (uu____73332, uu____73335)  in
                    match uu____73323 with
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
                 (uu____73378,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  uu____73379))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____73400 =
                      let uu____73409 = maybe_inline t11  in
                      let uu____73412 = maybe_inline t21  in
                      (uu____73409, uu____73412)  in
                    match uu____73400 with
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
             | MisMatch uu____73467 -> fail1 n_delta r t11 t21
             | uu____73476 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____73491 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____73491
           then
             let uu____73496 = FStar_Syntax_Print.term_to_string t1  in
             let uu____73498 = FStar_Syntax_Print.term_to_string t2  in
             let uu____73500 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____73508 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____73525 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____73525
                    (fun uu____73560  ->
                       match uu____73560 with
                       | (t11,t21) ->
                           let uu____73568 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____73570 =
                             let uu____73572 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____73572  in
                           Prims.op_Hat uu____73568 uu____73570))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____73496 uu____73498 uu____73500 uu____73508
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____73589 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____73589 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___609_73604  ->
    match uu___609_73604 with
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
      let uu___1789_73653 = p  in
      let uu____73656 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____73657 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1789_73653.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____73656;
        FStar_TypeChecker_Common.relation =
          (uu___1789_73653.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____73657;
        FStar_TypeChecker_Common.element =
          (uu___1789_73653.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1789_73653.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1789_73653.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1789_73653.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1789_73653.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1789_73653.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____73672 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____73672
            (fun _73677  -> FStar_TypeChecker_Common.TProb _73677)
      | FStar_TypeChecker_Common.CProb uu____73678 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____73701 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____73701 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____73709 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____73709 with
           | (lh,lhs_args) ->
               let uu____73756 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____73756 with
                | (rh,rhs_args) ->
                    let uu____73803 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____73816,FStar_Syntax_Syntax.Tm_uvar uu____73817)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____73906 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____73933,uu____73934)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____73949,FStar_Syntax_Syntax.Tm_uvar uu____73950)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____73965,FStar_Syntax_Syntax.Tm_arrow
                         uu____73966) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_73996 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_73996.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_73996.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_73996.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_73996.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_73996.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_73996.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_73996.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_73996.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_73996.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____73999,FStar_Syntax_Syntax.Tm_type uu____74000)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_74016 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_74016.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_74016.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_74016.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_74016.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_74016.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_74016.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_74016.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_74016.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_74016.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____74019,FStar_Syntax_Syntax.Tm_uvar uu____74020)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_74036 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_74036.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_74036.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_74036.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_74036.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_74036.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_74036.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_74036.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_74036.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_74036.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____74039,FStar_Syntax_Syntax.Tm_uvar uu____74040)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____74055,uu____74056)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____74071,FStar_Syntax_Syntax.Tm_uvar uu____74072)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____74087,uu____74088) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____73803 with
                     | (rank,tp1) ->
                         let uu____74101 =
                           FStar_All.pipe_right
                             (let uu___1860_74105 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1860_74105.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1860_74105.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1860_74105.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1860_74105.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1860_74105.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1860_74105.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1860_74105.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1860_74105.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1860_74105.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _74108  ->
                                FStar_TypeChecker_Common.TProb _74108)
                            in
                         (rank, uu____74101))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____74112 =
            FStar_All.pipe_right
              (let uu___1864_74116 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1864_74116.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1864_74116.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1864_74116.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1864_74116.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1864_74116.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1864_74116.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1864_74116.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1864_74116.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1864_74116.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _74119  -> FStar_TypeChecker_Common.CProb _74119)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____74112)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____74179 probs =
      match uu____74179 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____74260 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____74281 = rank wl.tcenv hd1  in
               (match uu____74281 with
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
                      (let uu____74342 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____74347 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____74347)
                          in
                       if uu____74342
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
          let uu____74420 = FStar_Syntax_Util.head_and_args t  in
          match uu____74420 with
          | (hd1,uu____74439) ->
              let uu____74464 =
                let uu____74465 = FStar_Syntax_Subst.compress hd1  in
                uu____74465.FStar_Syntax_Syntax.n  in
              (match uu____74464 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____74470) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____74505  ->
                           match uu____74505 with
                           | (y,uu____74514) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____74537  ->
                                       match uu____74537 with
                                       | (x,uu____74546) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____74551 -> false)
           in
        let uu____74553 = rank tcenv p  in
        match uu____74553 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____74562 -> true
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
    match projectee with | UDeferred _0 -> true | uu____74599 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____74619 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____74640 -> false
  
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
                        let uu____74703 = FStar_Syntax_Util.univ_kernel u3
                           in
                        match uu____74703 with
                        | (k,uu____74711) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____74724 -> false)))
            | uu____74726 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____74778 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____74786 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____74786 = (Prims.parse_int "0")))
                           in
                        if uu____74778 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____74807 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____74815 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____74815 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____74807)
               in
            let uu____74819 = filter1 u12  in
            let uu____74822 = filter1 u22  in (uu____74819, uu____74822)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then UFailed "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____74857 = filter_out_common_univs us1 us2  in
                   (match uu____74857 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____74917 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____74917 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____74920 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          (let uu____74931 =
                             let uu____74933 =
                               FStar_Syntax_Print.univ_to_string u12  in
                             let uu____74935 =
                               FStar_Syntax_Print.univ_to_string u22  in
                             FStar_Util.format2
                               "Unable to unify universes: %s and %s"
                               uu____74933 uu____74935
                              in
                           UFailed uu____74931))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____74961 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____74961 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____74987 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____74987 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____74990 ->
                   let uu____74995 =
                     let uu____74997 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____74999 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format3
                       "Unable to unify universes: %s and %s (%s)"
                       uu____74997 uu____74999 msg
                      in
                   UFailed uu____74995)
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____75002,uu____75003) ->
              let uu____75005 =
                let uu____75007 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____75009 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____75007 uu____75009
                 in
              failwith uu____75005
          | (FStar_Syntax_Syntax.U_unknown ,uu____75012) ->
              let uu____75013 =
                let uu____75015 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____75017 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____75015 uu____75017
                 in
              failwith uu____75013
          | (uu____75020,FStar_Syntax_Syntax.U_bvar uu____75021) ->
              let uu____75023 =
                let uu____75025 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____75027 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____75025 uu____75027
                 in
              failwith uu____75023
          | (uu____75030,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____75031 =
                let uu____75033 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____75035 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____75033 uu____75035
                 in
              failwith uu____75031
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____75065 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____75065
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____75082 = occurs_univ v1 u3  in
              if uu____75082
              then
                let uu____75085 =
                  let uu____75087 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____75089 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____75087 uu____75089
                   in
                try_umax_components u11 u21 uu____75085
              else
                (let uu____75094 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____75094)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____75106 = occurs_univ v1 u3  in
              if uu____75106
              then
                let uu____75109 =
                  let uu____75111 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____75113 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____75111 uu____75113
                   in
                try_umax_components u11 u21 uu____75109
              else
                (let uu____75118 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____75118)
          | (FStar_Syntax_Syntax.U_max uu____75119,uu____75120) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____75128 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____75128
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____75134,FStar_Syntax_Syntax.U_max uu____75135) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____75143 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____75143
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____75149,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____75151,FStar_Syntax_Syntax.U_name uu____75152) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____75154) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____75156) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____75158,FStar_Syntax_Syntax.U_succ uu____75159) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____75161,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____75268 = bc1  in
      match uu____75268 with
      | (bs1,mk_cod1) ->
          let uu____75312 = bc2  in
          (match uu____75312 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____75423 = aux xs ys  in
                     (match uu____75423 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____75506 =
                       let uu____75513 = mk_cod1 xs  in ([], uu____75513)  in
                     let uu____75516 =
                       let uu____75523 = mk_cod2 ys  in ([], uu____75523)  in
                     (uu____75506, uu____75516)
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
                  let uu____75592 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____75592 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____75595 =
                    let uu____75596 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____75596 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____75595
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____75601 = has_type_guard t1 t2  in (uu____75601, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____75602 = has_type_guard t2 t1  in (uu____75602, wl)
  
let is_flex_pat :
  'Auu____75612 'Auu____75613 'Auu____75614 .
    ('Auu____75612 * 'Auu____75613 * 'Auu____75614 Prims.list) -> Prims.bool
  =
  fun uu___610_75628  ->
    match uu___610_75628 with
    | (uu____75637,uu____75638,[]) -> true
    | uu____75642 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____75675 = f  in
      match uu____75675 with
      | (uu____75682,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____75683;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____75684;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____75687;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____75688;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____75689;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____75690;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____75760  ->
                 match uu____75760 with
                 | (y,uu____75769) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____75923 =
                  let uu____75938 =
                    let uu____75941 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____75941  in
                  ((FStar_List.rev pat_binders), uu____75938)  in
                FStar_Pervasives_Native.Some uu____75923
            | (uu____75974,[]) ->
                let uu____76005 =
                  let uu____76020 =
                    let uu____76023 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____76023  in
                  ((FStar_List.rev pat_binders), uu____76020)  in
                FStar_Pervasives_Native.Some uu____76005
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____76114 =
                  let uu____76115 = FStar_Syntax_Subst.compress a  in
                  uu____76115.FStar_Syntax_Syntax.n  in
                (match uu____76114 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____76135 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____76135
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___2188_76165 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___2188_76165.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___2188_76165.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____76169 =
                            let uu____76170 =
                              let uu____76177 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____76177)  in
                            FStar_Syntax_Syntax.NT uu____76170  in
                          [uu____76169]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___2194_76193 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2194_76193.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2194_76193.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____76194 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____76234 =
                  let uu____76249 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____76249  in
                (match uu____76234 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____76324 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____76357 ->
               let uu____76358 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____76358 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____76680 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____76680
       then
         let uu____76685 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____76685
       else ());
      (let uu____76690 = next_prob probs  in
       match uu____76690 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___2219_76717 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___2219_76717.wl_deferred);
               ctr = (uu___2219_76717.ctr);
               defer_ok = (uu___2219_76717.defer_ok);
               smt_ok = (uu___2219_76717.smt_ok);
               umax_heuristic_ok = (uu___2219_76717.umax_heuristic_ok);
               tcenv = (uu___2219_76717.tcenv);
               wl_implicits = (uu___2219_76717.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____76726 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____76726
                 then
                   let uu____76729 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____76729
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
                           (let uu___2231_76741 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___2231_76741.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___2231_76741.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___2231_76741.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___2231_76741.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___2231_76741.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___2231_76741.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___2231_76741.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___2231_76741.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___2231_76741.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____76767 ->
                let uu____76778 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____76849  ->
                          match uu____76849 with
                          | (c,uu____76860,uu____76861) -> c < probs.ctr))
                   in
                (match uu____76778 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____76916 =
                            let uu____76921 =
                              FStar_List.map
                                (fun uu____76939  ->
                                   match uu____76939 with
                                   | (uu____76953,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____76921, (probs.wl_implicits))  in
                          Success uu____76916
                      | uu____76961 ->
                          let uu____76972 =
                            let uu___2249_76973 = probs  in
                            let uu____76974 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____76997  ->
                                      match uu____76997 with
                                      | (uu____77006,uu____77007,y) -> y))
                               in
                            {
                              attempting = uu____76974;
                              wl_deferred = rest;
                              ctr = (uu___2249_76973.ctr);
                              defer_ok = (uu___2249_76973.defer_ok);
                              smt_ok = (uu___2249_76973.smt_ok);
                              umax_heuristic_ok =
                                (uu___2249_76973.umax_heuristic_ok);
                              tcenv = (uu___2249_76973.tcenv);
                              wl_implicits = (uu___2249_76973.wl_implicits)
                            }  in
                          solve env uu____76972))))

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
            let uu____77018 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____77018 with
            | USolved wl1 ->
                let uu____77020 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____77020
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
                  let uu____77074 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____77074 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____77077 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____77090;
                  FStar_Syntax_Syntax.vars = uu____77091;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____77094;
                  FStar_Syntax_Syntax.vars = uu____77095;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____77108,uu____77109) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____77117,FStar_Syntax_Syntax.Tm_uinst uu____77118) ->
                failwith "Impossible: expect head symbols to match"
            | uu____77126 -> USolved wl

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
            ((let uu____77138 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____77138
              then
                let uu____77143 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____77143 msg
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
               let uu____77235 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____77235 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____77290 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____77290
                then
                  let uu____77295 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____77297 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____77295 uu____77297
                else ());
               (let uu____77302 = head_matches_delta env1 wl2 t1 t2  in
                match uu____77302 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____77348 = eq_prob t1 t2 wl2  in
                         (match uu____77348 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____77369 ->
                         let uu____77378 = eq_prob t1 t2 wl2  in
                         (match uu____77378 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____77428 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____77443 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____77444 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____77443, uu____77444)
                           | FStar_Pervasives_Native.None  ->
                               let uu____77449 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____77450 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____77449, uu____77450)
                            in
                         (match uu____77428 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____77481 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____77481 with
                                | (t1_hd,t1_args) ->
                                    let uu____77526 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____77526 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____77592 =
                                              let uu____77599 =
                                                let uu____77610 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____77610 :: t1_args  in
                                              let uu____77627 =
                                                let uu____77636 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____77636 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____77685  ->
                                                   fun uu____77686  ->
                                                     fun uu____77687  ->
                                                       match (uu____77685,
                                                               uu____77686,
                                                               uu____77687)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____77737),
                                                          (a2,uu____77739))
                                                           ->
                                                           let uu____77776 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____77776
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____77599
                                                uu____77627
                                               in
                                            match uu____77592 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___2403_77802 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___2403_77802.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___2403_77802.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___2403_77802.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____77814 =
                                                  solve env1 wl'  in
                                                (match uu____77814 with
                                                 | Success (uu____77817,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___2412_77821
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___2412_77821.attempting);
                                                            wl_deferred =
                                                              (uu___2412_77821.wl_deferred);
                                                            ctr =
                                                              (uu___2412_77821.ctr);
                                                            defer_ok =
                                                              (uu___2412_77821.defer_ok);
                                                            smt_ok =
                                                              (uu___2412_77821.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___2412_77821.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___2412_77821.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____77822 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____77855 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____77855 with
                                | (t1_base,p1_opt) ->
                                    let uu____77891 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____77891 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____77990 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____77990
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
                                               let uu____78043 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____78043
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
                                               let uu____78075 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____78075
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
                                               let uu____78107 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____78107
                                           | uu____78110 -> t_base  in
                                         let uu____78127 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____78127 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____78141 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____78141, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____78148 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____78148 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____78184 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____78184 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____78220 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____78220
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
                              let uu____78244 = combine t11 t21 wl2  in
                              (match uu____78244 with
                               | (t12,ps,wl3) ->
                                   ((let uu____78277 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____78277
                                     then
                                       let uu____78282 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____78282
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____78324 ts1 =
               match uu____78324 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____78387 = pairwise out t wl2  in
                        (match uu____78387 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____78423 =
               let uu____78434 = FStar_List.hd ts  in (uu____78434, [], wl1)
                in
             let uu____78443 = FStar_List.tl ts  in
             aux uu____78423 uu____78443  in
           let uu____78450 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____78450 with
           | (this_flex,this_rigid) ->
               let uu____78476 =
                 let uu____78477 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____78477.FStar_Syntax_Syntax.n  in
               (match uu____78476 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____78502 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____78502
                    then
                      let uu____78505 = destruct_flex_t this_flex wl  in
                      (match uu____78505 with
                       | (flex,wl1) ->
                           let uu____78512 = quasi_pattern env flex  in
                           (match uu____78512 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____78531 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____78531
                                  then
                                    let uu____78536 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____78536
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____78543 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2514_78546 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2514_78546.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2514_78546.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2514_78546.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2514_78546.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2514_78546.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2514_78546.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2514_78546.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2514_78546.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2514_78546.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____78543)
                | uu____78547 ->
                    ((let uu____78549 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____78549
                      then
                        let uu____78554 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____78554
                      else ());
                     (let uu____78559 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____78559 with
                      | (u,_args) ->
                          let uu____78602 =
                            let uu____78603 = FStar_Syntax_Subst.compress u
                               in
                            uu____78603.FStar_Syntax_Syntax.n  in
                          (match uu____78602 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____78631 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____78631 with
                                 | (u',uu____78650) ->
                                     let uu____78675 =
                                       let uu____78676 = whnf env u'  in
                                       uu____78676.FStar_Syntax_Syntax.n  in
                                     (match uu____78675 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____78698 -> false)
                                  in
                               let uu____78700 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___611_78723  ->
                                         match uu___611_78723 with
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
                                              | uu____78737 -> false)
                                         | uu____78741 -> false))
                                  in
                               (match uu____78700 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____78756 = whnf env this_rigid
                                         in
                                      let uu____78757 =
                                        FStar_List.collect
                                          (fun uu___612_78763  ->
                                             match uu___612_78763 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____78769 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____78769]
                                             | uu____78773 -> [])
                                          bounds_probs
                                         in
                                      uu____78756 :: uu____78757  in
                                    let uu____78774 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____78774 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____78807 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____78822 =
                                               let uu____78823 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____78823.FStar_Syntax_Syntax.n
                                                in
                                             match uu____78822 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____78835 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____78835)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____78846 -> bound  in
                                           let uu____78847 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____78847)  in
                                         (match uu____78807 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____78882 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____78882
                                                then
                                                  let wl'1 =
                                                    let uu___2574_78888 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2574_78888.wl_deferred);
                                                      ctr =
                                                        (uu___2574_78888.ctr);
                                                      defer_ok =
                                                        (uu___2574_78888.defer_ok);
                                                      smt_ok =
                                                        (uu___2574_78888.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2574_78888.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2574_78888.tcenv);
                                                      wl_implicits =
                                                        (uu___2574_78888.wl_implicits)
                                                    }  in
                                                  let uu____78889 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____78889
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____78895 =
                                                  solve_t env eq_prob
                                                    (let uu___2579_78897 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2579_78897.wl_deferred);
                                                       ctr =
                                                         (uu___2579_78897.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2579_78897.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2579_78897.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2579_78897.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____78895 with
                                                | Success (uu____78899,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2585_78902 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2585_78902.wl_deferred);
                                                        ctr =
                                                          (uu___2585_78902.ctr);
                                                        defer_ok =
                                                          (uu___2585_78902.defer_ok);
                                                        smt_ok =
                                                          (uu___2585_78902.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2585_78902.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2585_78902.tcenv);
                                                        wl_implicits =
                                                          (uu___2585_78902.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2588_78904 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2588_78904.attempting);
                                                        wl_deferred =
                                                          (uu___2588_78904.wl_deferred);
                                                        ctr =
                                                          (uu___2588_78904.ctr);
                                                        defer_ok =
                                                          (uu___2588_78904.defer_ok);
                                                        smt_ok =
                                                          (uu___2588_78904.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2588_78904.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2588_78904.tcenv);
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
                                                    let uu____78920 =
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
                                                    ((let uu____78934 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____78934
                                                      then
                                                        let uu____78939 =
                                                          let uu____78941 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____78941
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____78939
                                                      else ());
                                                     (let uu____78954 =
                                                        let uu____78969 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____78969)
                                                         in
                                                      match uu____78954 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____78991))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____79017 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____79017
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
                                                                  let uu____79037
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____79037))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____79062 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____79062
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
                                                                    let uu____79082
                                                                    =
                                                                    let uu____79087
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____79087
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____79082
                                                                    [] wl2
                                                                     in
                                                                  let uu____79093
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____79093))))
                                                      | uu____79094 ->
                                                          giveup env
                                                            (Prims.op_Hat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____79110 when flip ->
                               let uu____79111 =
                                 let uu____79113 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____79115 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____79113 uu____79115
                                  in
                               failwith uu____79111
                           | uu____79118 ->
                               let uu____79119 =
                                 let uu____79121 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____79123 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____79121 uu____79123
                                  in
                               failwith uu____79119)))))

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
                      (fun uu____79159  ->
                         match uu____79159 with
                         | (x,i) ->
                             let uu____79178 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____79178, i)) bs_lhs
                     in
                  let uu____79181 = lhs  in
                  match uu____79181 with
                  | (uu____79182,u_lhs,uu____79184) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____79281 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____79291 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____79291, univ)
                             in
                          match uu____79281 with
                          | (k,univ) ->
                              let uu____79298 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____79298 with
                               | (uu____79315,u,wl3) ->
                                   let uu____79318 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____79318, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____79344 =
                              let uu____79357 =
                                let uu____79368 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____79368 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____79419  ->
                                   fun uu____79420  ->
                                     match (uu____79419, uu____79420) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____79521 =
                                           let uu____79528 =
                                             let uu____79531 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____79531
                                              in
                                           copy_uvar u_lhs [] uu____79528 wl2
                                            in
                                         (match uu____79521 with
                                          | (uu____79560,t_a,wl3) ->
                                              let uu____79563 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____79563 with
                                               | (uu____79582,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____79357
                                ([], wl1)
                               in
                            (match uu____79344 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2698_79638 = ct  in
                                   let uu____79639 =
                                     let uu____79642 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____79642
                                      in
                                   let uu____79657 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2698_79638.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2698_79638.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____79639;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____79657;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2698_79638.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2701_79675 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2701_79675.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2701_79675.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____79678 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____79678 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____79740 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____79740 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____79751 =
                                          let uu____79756 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____79756)  in
                                        TERM uu____79751  in
                                      let uu____79757 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____79757 with
                                       | (sub_prob,wl3) ->
                                           let uu____79771 =
                                             let uu____79772 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____79772
                                              in
                                           solve env uu____79771))
                             | (x,imp)::formals2 ->
                                 let uu____79794 =
                                   let uu____79801 =
                                     let uu____79804 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____79804
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____79801 wl1
                                    in
                                 (match uu____79794 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____79825 =
                                          let uu____79828 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____79828
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____79825 u_x
                                         in
                                      let uu____79829 =
                                        let uu____79832 =
                                          let uu____79835 =
                                            let uu____79836 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____79836, imp)  in
                                          [uu____79835]  in
                                        FStar_List.append bs_terms
                                          uu____79832
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____79829 formals2 wl2)
                              in
                           let uu____79863 = occurs_check u_lhs arrow1  in
                           (match uu____79863 with
                            | (uu____79876,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____79892 =
                                    let uu____79894 = FStar_Option.get msg
                                       in
                                    Prims.op_Hat "occurs-check failed: "
                                      uu____79894
                                     in
                                  giveup_or_defer env orig wl uu____79892
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
              (let uu____79927 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____79927
               then
                 let uu____79932 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____79935 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____79932 (rel_to_string (p_rel orig)) uu____79935
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____80062 = rhs wl1 scope env1 subst1  in
                     (match uu____80062 with
                      | (rhs_prob,wl2) ->
                          ((let uu____80083 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____80083
                            then
                              let uu____80088 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____80088
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____80166 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____80166 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2770_80168 = hd1  in
                       let uu____80169 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2770_80168.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2770_80168.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____80169
                       }  in
                     let hd21 =
                       let uu___2773_80173 = hd2  in
                       let uu____80174 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2773_80173.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2773_80173.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____80174
                       }  in
                     let uu____80177 =
                       let uu____80182 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____80182
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____80177 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____80203 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____80203
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____80210 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____80210 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____80277 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____80277
                                  in
                               ((let uu____80295 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____80295
                                 then
                                   let uu____80300 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____80302 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____80300
                                     uu____80302
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____80335 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____80371 = aux wl [] env [] bs1 bs2  in
               match uu____80371 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____80426 = attempt sub_probs wl2  in
                   solve env uu____80426)

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
            let uu___2808_80447 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2808_80447.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2808_80447.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____80460 = try_solve env wl'  in
          match uu____80460 with
          | Success (uu____80461,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2817_80465 = wl  in
                  {
                    attempting = (uu___2817_80465.attempting);
                    wl_deferred = (uu___2817_80465.wl_deferred);
                    ctr = (uu___2817_80465.ctr);
                    defer_ok = (uu___2817_80465.defer_ok);
                    smt_ok = (uu___2817_80465.smt_ok);
                    umax_heuristic_ok = (uu___2817_80465.umax_heuristic_ok);
                    tcenv = (uu___2817_80465.tcenv);
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
        (let uu____80477 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____80477 wl)

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
              let uu____80491 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____80491 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____80525 = lhs1  in
              match uu____80525 with
              | (uu____80528,ctx_u,uu____80530) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____80538 ->
                        let uu____80539 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____80539 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____80588 = quasi_pattern env1 lhs1  in
              match uu____80588 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____80622) ->
                  let uu____80627 = lhs1  in
                  (match uu____80627 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____80642 = occurs_check ctx_u rhs1  in
                       (match uu____80642 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____80693 =
                                let uu____80701 =
                                  let uu____80703 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____80703
                                   in
                                FStar_Util.Inl uu____80701  in
                              (uu____80693, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____80731 =
                                 let uu____80733 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____80733  in
                               if uu____80731
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____80760 =
                                    let uu____80768 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____80768  in
                                  let uu____80774 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____80760, uu____80774)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____80818 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____80818 with
              | (rhs_hd,args) ->
                  let uu____80861 = FStar_Util.prefix args  in
                  (match uu____80861 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____80933 = lhs1  in
                       (match uu____80933 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____80937 =
                              let uu____80948 =
                                let uu____80955 =
                                  let uu____80958 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____80958
                                   in
                                copy_uvar u_lhs [] uu____80955 wl1  in
                              match uu____80948 with
                              | (uu____80985,t_last_arg,wl2) ->
                                  let uu____80988 =
                                    let uu____80995 =
                                      let uu____80996 =
                                        let uu____81005 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____81005]  in
                                      FStar_List.append bs_lhs uu____80996
                                       in
                                    copy_uvar u_lhs uu____80995 t_res_lhs wl2
                                     in
                                  (match uu____80988 with
                                   | (uu____81040,lhs',wl3) ->
                                       let uu____81043 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____81043 with
                                        | (uu____81060,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____80937 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____81081 =
                                     let uu____81082 =
                                       let uu____81087 =
                                         let uu____81088 =
                                           let uu____81091 =
                                             let uu____81096 =
                                               let uu____81097 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____81097]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____81096
                                              in
                                           uu____81091
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____81088
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____81087)  in
                                     TERM uu____81082  in
                                   [uu____81081]  in
                                 let uu____81124 =
                                   let uu____81131 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____81131 with
                                   | (p1,wl3) ->
                                       let uu____81151 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____81151 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____81124 with
                                  | (sub_probs,wl3) ->
                                      let uu____81183 =
                                        let uu____81184 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____81184  in
                                      solve env1 uu____81183))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____81218 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____81218 with
                | (uu____81236,args) ->
                    (match args with | [] -> false | uu____81272 -> true)
                 in
              let is_arrow rhs2 =
                let uu____81291 =
                  let uu____81292 = FStar_Syntax_Subst.compress rhs2  in
                  uu____81292.FStar_Syntax_Syntax.n  in
                match uu____81291 with
                | FStar_Syntax_Syntax.Tm_arrow uu____81296 -> true
                | uu____81312 -> false  in
              let uu____81314 = quasi_pattern env1 lhs1  in
              match uu____81314 with
              | FStar_Pervasives_Native.None  ->
                  let uu____81325 =
                    let uu____81327 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                      uu____81327
                     in
                  giveup_or_defer env1 orig1 wl1 uu____81325
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____81336 = is_app rhs1  in
                  if uu____81336
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____81341 = is_arrow rhs1  in
                     if uu____81341
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____81346 =
                          let uu____81348 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heuristic cannot solve %s; rhs not an app or arrow"
                            uu____81348
                           in
                        giveup_or_defer env1 orig1 wl1 uu____81346))
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
                let uu____81359 = lhs  in
                (match uu____81359 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____81363 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____81363 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____81381 =
                              let uu____81385 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____81385
                               in
                            FStar_All.pipe_right uu____81381
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____81406 = occurs_check ctx_uv rhs1  in
                          (match uu____81406 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____81435 =
                                   let uu____81437 = FStar_Option.get msg  in
                                   Prims.op_Hat "occurs-check failed: "
                                     uu____81437
                                    in
                                 giveup_or_defer env orig wl uu____81435
                               else
                                 (let uu____81443 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____81443
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____81450 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____81450
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____81454 =
                                         let uu____81456 =
                                           names_to_string1 fvs2  in
                                         let uu____81458 =
                                           names_to_string1 fvs1  in
                                         let uu____81460 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____81456 uu____81458
                                           uu____81460
                                          in
                                       giveup_or_defer env orig wl
                                         uu____81454)
                                    else first_order orig env wl lhs rhs1))
                      | uu____81472 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____81479 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____81479 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____81505 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____81505
                             | (FStar_Util.Inl msg,uu____81507) ->
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
                  (let uu____81552 =
                     let uu____81569 = quasi_pattern env lhs  in
                     let uu____81576 = quasi_pattern env rhs  in
                     (uu____81569, uu____81576)  in
                   match uu____81552 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____81619 = lhs  in
                       (match uu____81619 with
                        | ({ FStar_Syntax_Syntax.n = uu____81620;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____81622;_},u_lhs,uu____81624)
                            ->
                            let uu____81627 = rhs  in
                            (match uu____81627 with
                             | (uu____81628,u_rhs,uu____81630) ->
                                 let uu____81631 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____81631
                                 then
                                   let uu____81638 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____81638
                                 else
                                   (let uu____81641 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____81641 with
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
                                        let uu____81673 =
                                          let uu____81680 =
                                            let uu____81683 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____81683
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____81680
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____81673 with
                                         | (uu____81695,w,wl1) ->
                                             let w_app =
                                               let uu____81701 =
                                                 let uu____81706 =
                                                   FStar_List.map
                                                     (fun uu____81717  ->
                                                        match uu____81717
                                                        with
                                                        | (z,uu____81725) ->
                                                            let uu____81730 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____81730) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____81706
                                                  in
                                               uu____81701
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____81734 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____81734
                                               then
                                                 let uu____81739 =
                                                   let uu____81743 =
                                                     flex_t_to_string lhs  in
                                                   let uu____81745 =
                                                     let uu____81749 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____81751 =
                                                       let uu____81755 =
                                                         term_to_string w  in
                                                       let uu____81757 =
                                                         let uu____81761 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____81770 =
                                                           let uu____81774 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____81783 =
                                                             let uu____81787
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____81787]
                                                              in
                                                           uu____81774 ::
                                                             uu____81783
                                                            in
                                                         uu____81761 ::
                                                           uu____81770
                                                          in
                                                       uu____81755 ::
                                                         uu____81757
                                                        in
                                                     uu____81749 ::
                                                       uu____81751
                                                      in
                                                   uu____81743 :: uu____81745
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____81739
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____81804 =
                                                     let uu____81809 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____81809)  in
                                                   TERM uu____81804  in
                                                 let uu____81810 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____81810
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____81818 =
                                                        let uu____81823 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____81823)
                                                         in
                                                      TERM uu____81818  in
                                                    [s1; s2])
                                                  in
                                               let uu____81824 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____81824))))))
                   | uu____81825 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____81896 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____81896
            then
              let uu____81901 = FStar_Syntax_Print.term_to_string t1  in
              let uu____81903 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____81905 = FStar_Syntax_Print.term_to_string t2  in
              let uu____81907 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____81901 uu____81903 uu____81905 uu____81907
            else ());
           (let uu____81918 = FStar_Syntax_Util.head_and_args t1  in
            match uu____81918 with
            | (head1,args1) ->
                let uu____81961 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____81961 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____82031 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____82031 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              k false (defer "universe constraints" orig wl3))
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____82061 =
                         let uu____82063 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____82065 = args_to_string args1  in
                         let uu____82069 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____82071 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____82063 uu____82065 uu____82069 uu____82071
                          in
                       giveup env1 uu____82061 orig
                     else
                       (let uu____82078 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____82087 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____82087 = FStar_Syntax_Util.Equal)
                           in
                        if uu____82078
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___3066_82091 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___3066_82091.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___3066_82091.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___3066_82091.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___3066_82091.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___3066_82091.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___3066_82091.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___3066_82091.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___3066_82091.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____82101 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____82101
                                    else solve env1 wl2))
                        else
                          (let uu____82106 = base_and_refinement env1 t1  in
                           match uu____82106 with
                           | (base1,refinement1) ->
                               let uu____82131 = base_and_refinement env1 t2
                                  in
                               (match uu____82131 with
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
                                           let uu____82296 =
                                             FStar_List.fold_right
                                               (fun uu____82336  ->
                                                  fun uu____82337  ->
                                                    match (uu____82336,
                                                            uu____82337)
                                                    with
                                                    | (((a1,uu____82389),
                                                        (a2,uu____82391)),
                                                       (probs,wl3)) ->
                                                        let uu____82440 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____82440
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____82296 with
                                           | (subprobs,wl3) ->
                                               ((let uu____82483 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____82483
                                                 then
                                                   let uu____82488 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____82488
                                                 else ());
                                                (let uu____82494 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____82494
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
                                                    (let uu____82521 =
                                                       mk_sub_probs wl3  in
                                                     match uu____82521 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____82537 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____82537
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____82545 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____82545))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____82569 =
                                                    mk_sub_probs wl3  in
                                                  match uu____82569 with
                                                  | (subprobs,wl4) ->
                                                      let wl5 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          [] wl4
                                                         in
                                                      let uu____82583 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____82583)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____82609 =
                                           match uu____82609 with
                                           | (prob,reason) ->
                                               ((let uu____82620 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____82620
                                                 then
                                                   let uu____82625 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____82627 =
                                                     prob_to_string env2 prob
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____82625 uu____82627
                                                     reason
                                                 else ());
                                                (let uu____82632 =
                                                   let uu____82641 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____82644 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____82641, uu____82644)
                                                    in
                                                 match uu____82632 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____82657 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____82657 with
                                                      | (head1',uu____82675)
                                                          ->
                                                          let uu____82700 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____82700
                                                           with
                                                           | (head2',uu____82718)
                                                               ->
                                                               let uu____82743
                                                                 =
                                                                 let uu____82748
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____82749
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____82748,
                                                                   uu____82749)
                                                                  in
                                                               (match uu____82743
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____82751
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____82751
                                                                    then
                                                                    let uu____82756
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____82758
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____82760
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____82762
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____82756
                                                                    uu____82758
                                                                    uu____82760
                                                                    uu____82762
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____82767
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___3152_82775
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___3152_82775.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___3152_82775.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___3152_82775.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___3152_82775.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___3152_82775.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___3152_82775.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___3152_82775.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___3152_82775.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____82777
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____82777
                                                                    then
                                                                    let uu____82782
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____82782
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____82787 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____82799 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____82799 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____82807 =
                                             let uu____82808 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____82808.FStar_Syntax_Syntax.n
                                              in
                                           match uu____82807 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____82813 -> false  in
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
                                          | uu____82816 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____82819 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___3172_82855 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___3172_82855.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___3172_82855.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___3172_82855.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___3172_82855.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___3172_82855.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___3172_82855.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___3172_82855.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___3172_82855.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____82931 = destruct_flex_t scrutinee wl1  in
             match uu____82931 with
             | ((_t,uv,_args),wl2) ->
                 let uu____82942 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____82942 with
                  | (xs,pat_term,uu____82958,uu____82959) ->
                      let uu____82964 =
                        FStar_List.fold_left
                          (fun uu____82987  ->
                             fun x  ->
                               match uu____82987 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____83008 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____83008 with
                                    | (uu____83027,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____82964 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____83048 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____83048 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___3212_83065 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___3212_83065.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___3212_83065.umax_heuristic_ok);
                                    tcenv = (uu___3212_83065.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____83077 = solve env1 wl'  in
                                (match uu____83077 with
                                 | Success (uu____83080,imps) ->
                                     let wl'1 =
                                       let uu___3220_83083 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___3220_83083.wl_deferred);
                                         ctr = (uu___3220_83083.ctr);
                                         defer_ok =
                                           (uu___3220_83083.defer_ok);
                                         smt_ok = (uu___3220_83083.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___3220_83083.umax_heuristic_ok);
                                         tcenv = (uu___3220_83083.tcenv);
                                         wl_implicits =
                                           (uu___3220_83083.wl_implicits)
                                       }  in
                                     let uu____83084 = solve env1 wl'1  in
                                     (match uu____83084 with
                                      | Success (uu____83087,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___3228_83091 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___3228_83091.attempting);
                                                 wl_deferred =
                                                   (uu___3228_83091.wl_deferred);
                                                 ctr = (uu___3228_83091.ctr);
                                                 defer_ok =
                                                   (uu___3228_83091.defer_ok);
                                                 smt_ok =
                                                   (uu___3228_83091.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3228_83091.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3228_83091.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____83092 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____83099 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____83122 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____83122
                 then
                   let uu____83127 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____83129 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____83127 uu____83129
                 else ());
                (let uu____83134 =
                   let uu____83155 =
                     let uu____83164 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____83164)  in
                   let uu____83171 =
                     let uu____83180 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____83180)  in
                   (uu____83155, uu____83171)  in
                 match uu____83134 with
                 | ((uu____83210,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____83213;
                                   FStar_Syntax_Syntax.vars = uu____83214;_}),
                    (s,t)) ->
                     let uu____83285 =
                       let uu____83287 = is_flex scrutinee  in
                       Prims.op_Negation uu____83287  in
                     if uu____83285
                     then
                       ((let uu____83298 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____83298
                         then
                           let uu____83303 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____83303
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____83322 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____83322
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____83337 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____83337
                           then
                             let uu____83342 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____83344 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____83342 uu____83344
                           else ());
                          (let pat_discriminates uu___613_83369 =
                             match uu___613_83369 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____83385;
                                  FStar_Syntax_Syntax.p = uu____83386;_},FStar_Pervasives_Native.None
                                ,uu____83387) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____83401;
                                  FStar_Syntax_Syntax.p = uu____83402;_},FStar_Pervasives_Native.None
                                ,uu____83403) -> true
                             | uu____83430 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____83533 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____83533 with
                                       | (uu____83535,uu____83536,t') ->
                                           let uu____83554 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____83554 with
                                            | (FullMatch ,uu____83566) ->
                                                true
                                            | (HeadMatch
                                               uu____83580,uu____83581) ->
                                                true
                                            | uu____83596 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____83633 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____83633
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____83644 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____83644 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____83732,uu____83733) ->
                                       branches1
                                   | uu____83878 -> branches  in
                                 let uu____83933 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____83942 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____83942 with
                                        | (p,uu____83946,uu____83947) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _83976  -> FStar_Util.Inr _83976)
                                   uu____83933))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____84006 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____84006 with
                                | (p,uu____84015,e) ->
                                    ((let uu____84034 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____84034
                                      then
                                        let uu____84039 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____84041 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____84039 uu____84041
                                      else ());
                                     (let uu____84046 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _84061  -> FStar_Util.Inr _84061)
                                        uu____84046)))))
                 | ((s,t),(uu____84064,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____84067;
                                         FStar_Syntax_Syntax.vars =
                                           uu____84068;_}))
                     ->
                     let uu____84137 =
                       let uu____84139 = is_flex scrutinee  in
                       Prims.op_Negation uu____84139  in
                     if uu____84137
                     then
                       ((let uu____84150 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____84150
                         then
                           let uu____84155 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____84155
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____84174 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____84174
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____84189 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____84189
                           then
                             let uu____84194 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____84196 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____84194 uu____84196
                           else ());
                          (let pat_discriminates uu___613_84221 =
                             match uu___613_84221 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____84237;
                                  FStar_Syntax_Syntax.p = uu____84238;_},FStar_Pervasives_Native.None
                                ,uu____84239) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____84253;
                                  FStar_Syntax_Syntax.p = uu____84254;_},FStar_Pervasives_Native.None
                                ,uu____84255) -> true
                             | uu____84282 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____84385 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____84385 with
                                       | (uu____84387,uu____84388,t') ->
                                           let uu____84406 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____84406 with
                                            | (FullMatch ,uu____84418) ->
                                                true
                                            | (HeadMatch
                                               uu____84432,uu____84433) ->
                                                true
                                            | uu____84448 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____84485 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____84485
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____84496 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____84496 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____84584,uu____84585) ->
                                       branches1
                                   | uu____84730 -> branches  in
                                 let uu____84785 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____84794 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____84794 with
                                        | (p,uu____84798,uu____84799) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _84828  -> FStar_Util.Inr _84828)
                                   uu____84785))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____84858 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____84858 with
                                | (p,uu____84867,e) ->
                                    ((let uu____84886 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____84886
                                      then
                                        let uu____84891 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____84893 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____84891 uu____84893
                                      else ());
                                     (let uu____84898 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _84913  -> FStar_Util.Inr _84913)
                                        uu____84898)))))
                 | uu____84914 ->
                     ((let uu____84936 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____84936
                       then
                         let uu____84941 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____84943 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____84941 uu____84943
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____84989 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____84989
            then
              let uu____84994 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____84996 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____84998 = FStar_Syntax_Print.term_to_string t1  in
              let uu____85000 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____84994 uu____84996 uu____84998 uu____85000
            else ());
           (let uu____85005 = head_matches_delta env1 wl1 t1 t2  in
            match uu____85005 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____85036,uu____85037) ->
                     let rec may_relate head3 =
                       let uu____85065 =
                         let uu____85066 = FStar_Syntax_Subst.compress head3
                            in
                         uu____85066.FStar_Syntax_Syntax.n  in
                       match uu____85065 with
                       | FStar_Syntax_Syntax.Tm_name uu____85070 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____85072 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____85097 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____85097 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____85099 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____85102
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____85103 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____85106,uu____85107) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____85149) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____85155) ->
                           may_relate t
                       | uu____85160 -> false  in
                     let uu____85162 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____85162 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____85183 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____85183
                          then
                            let uu____85186 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____85186 with
                             | (guard,wl2) ->
                                 let uu____85193 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____85193)
                          else
                            (let uu____85196 =
                               let uu____85198 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____85200 =
                                 let uu____85202 =
                                   let uu____85206 =
                                     delta_depth_of_term env1 head1  in
                                   FStar_Util.bind_opt uu____85206
                                     (fun x  ->
                                        let uu____85213 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____85213)
                                    in
                                 FStar_Util.dflt "" uu____85202  in
                               let uu____85218 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               let uu____85220 =
                                 let uu____85222 =
                                   let uu____85226 =
                                     delta_depth_of_term env1 head2  in
                                   FStar_Util.bind_opt uu____85226
                                     (fun x  ->
                                        let uu____85233 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____85233)
                                    in
                                 FStar_Util.dflt "" uu____85222  in
                               FStar_Util.format4
                                 "head mismatch (%s (%s) vs %s (%s))"
                                 uu____85198 uu____85200 uu____85218
                                 uu____85220
                                in
                             giveup env1 uu____85196 orig))
                 | (HeadMatch (true ),uu____85239) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____85254 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____85254 with
                        | (guard,wl2) ->
                            let uu____85261 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____85261)
                     else
                       (let uu____85264 =
                          let uu____85266 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____85268 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____85266 uu____85268
                           in
                        giveup env1 uu____85264 orig)
                 | (uu____85271,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___3401_85285 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___3401_85285.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___3401_85285.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___3401_85285.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___3401_85285.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___3401_85285.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___3401_85285.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___3401_85285.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___3401_85285.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____85312 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____85312
          then
            let uu____85315 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____85315
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____85321 =
                let uu____85324 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____85324  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____85321 t1);
             (let uu____85343 =
                let uu____85346 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____85346  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____85343 t2);
             (let uu____85365 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____85365
              then
                let uu____85369 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____85371 =
                  let uu____85373 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____85375 =
                    let uu____85377 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____85377  in
                  Prims.op_Hat uu____85373 uu____85375  in
                let uu____85380 =
                  let uu____85382 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____85384 =
                    let uu____85386 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____85386  in
                  Prims.op_Hat uu____85382 uu____85384  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____85369 uu____85371 uu____85380
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____85393,uu____85394) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____85418,FStar_Syntax_Syntax.Tm_delayed uu____85419) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____85443,uu____85444) ->
                  let uu____85471 =
                    let uu___3432_85472 = problem  in
                    let uu____85473 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3432_85472.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____85473;
                      FStar_TypeChecker_Common.relation =
                        (uu___3432_85472.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3432_85472.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3432_85472.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3432_85472.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3432_85472.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3432_85472.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3432_85472.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3432_85472.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____85471 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____85474,uu____85475) ->
                  let uu____85482 =
                    let uu___3438_85483 = problem  in
                    let uu____85484 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3438_85483.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____85484;
                      FStar_TypeChecker_Common.relation =
                        (uu___3438_85483.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3438_85483.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3438_85483.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3438_85483.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3438_85483.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3438_85483.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3438_85483.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3438_85483.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____85482 wl
              | (uu____85485,FStar_Syntax_Syntax.Tm_ascribed uu____85486) ->
                  let uu____85513 =
                    let uu___3444_85514 = problem  in
                    let uu____85515 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3444_85514.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3444_85514.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3444_85514.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____85515;
                      FStar_TypeChecker_Common.element =
                        (uu___3444_85514.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3444_85514.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3444_85514.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3444_85514.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3444_85514.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3444_85514.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____85513 wl
              | (uu____85516,FStar_Syntax_Syntax.Tm_meta uu____85517) ->
                  let uu____85524 =
                    let uu___3450_85525 = problem  in
                    let uu____85526 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3450_85525.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3450_85525.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3450_85525.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____85526;
                      FStar_TypeChecker_Common.element =
                        (uu___3450_85525.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3450_85525.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3450_85525.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3450_85525.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3450_85525.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3450_85525.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____85524 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____85528),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____85530)) ->
                  let uu____85539 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____85539
              | (FStar_Syntax_Syntax.Tm_bvar uu____85540,uu____85541) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____85543,FStar_Syntax_Syntax.Tm_bvar uu____85544) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___614_85614 =
                    match uu___614_85614 with
                    | [] -> c
                    | bs ->
                        let uu____85642 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____85642
                     in
                  let uu____85653 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____85653 with
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
                                    let uu____85802 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____85802
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
                  let mk_t t l uu___615_85891 =
                    match uu___615_85891 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____85933 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____85933 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____86078 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____86079 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____86078
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____86079 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____86081,uu____86082) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____86113 -> true
                    | uu____86133 -> false  in
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
                      (let uu____86193 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3552_86201 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3552_86201.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3552_86201.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3552_86201.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3552_86201.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3552_86201.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3552_86201.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3552_86201.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3552_86201.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3552_86201.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___3552_86201.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3552_86201.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3552_86201.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3552_86201.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3552_86201.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3552_86201.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3552_86201.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3552_86201.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3552_86201.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3552_86201.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3552_86201.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3552_86201.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3552_86201.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3552_86201.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3552_86201.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3552_86201.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3552_86201.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3552_86201.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3552_86201.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3552_86201.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3552_86201.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3552_86201.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3552_86201.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3552_86201.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3552_86201.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3552_86201.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3552_86201.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3552_86201.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3552_86201.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3552_86201.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3552_86201.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____86193 with
                       | (uu____86206,ty,uu____86208) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____86217 =
                                 let uu____86218 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____86218.FStar_Syntax_Syntax.n  in
                               match uu____86217 with
                               | FStar_Syntax_Syntax.Tm_refine uu____86221 ->
                                   let uu____86228 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____86228
                               | uu____86229 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____86232 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____86232
                             then
                               let uu____86237 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____86239 =
                                 let uu____86241 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____86241
                                  in
                               let uu____86242 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____86237 uu____86239 uu____86242
                             else ());
                            r1))
                     in
                  let uu____86247 =
                    let uu____86264 = maybe_eta t1  in
                    let uu____86271 = maybe_eta t2  in
                    (uu____86264, uu____86271)  in
                  (match uu____86247 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3573_86313 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3573_86313.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3573_86313.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3573_86313.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3573_86313.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3573_86313.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3573_86313.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3573_86313.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3573_86313.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____86334 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____86334
                       then
                         let uu____86337 = destruct_flex_t not_abs wl  in
                         (match uu____86337 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_86354 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_86354.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_86354.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_86354.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_86354.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_86354.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_86354.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_86354.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_86354.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____86378 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____86378
                       then
                         let uu____86381 = destruct_flex_t not_abs wl  in
                         (match uu____86381 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_86398 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_86398.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_86398.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_86398.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_86398.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_86398.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_86398.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_86398.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_86398.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____86402 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____86420,FStar_Syntax_Syntax.Tm_abs uu____86421) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____86452 -> true
                    | uu____86472 -> false  in
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
                      (let uu____86532 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3552_86540 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3552_86540.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3552_86540.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3552_86540.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3552_86540.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3552_86540.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3552_86540.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3552_86540.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3552_86540.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3552_86540.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___3552_86540.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3552_86540.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3552_86540.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3552_86540.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3552_86540.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3552_86540.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3552_86540.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3552_86540.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3552_86540.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3552_86540.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3552_86540.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3552_86540.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3552_86540.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3552_86540.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3552_86540.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3552_86540.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3552_86540.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3552_86540.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3552_86540.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3552_86540.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3552_86540.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3552_86540.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3552_86540.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3552_86540.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3552_86540.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3552_86540.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3552_86540.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3552_86540.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3552_86540.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3552_86540.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3552_86540.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____86532 with
                       | (uu____86545,ty,uu____86547) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____86556 =
                                 let uu____86557 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____86557.FStar_Syntax_Syntax.n  in
                               match uu____86556 with
                               | FStar_Syntax_Syntax.Tm_refine uu____86560 ->
                                   let uu____86567 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____86567
                               | uu____86568 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____86571 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____86571
                             then
                               let uu____86576 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____86578 =
                                 let uu____86580 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____86580
                                  in
                               let uu____86581 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____86576 uu____86578 uu____86581
                             else ());
                            r1))
                     in
                  let uu____86586 =
                    let uu____86603 = maybe_eta t1  in
                    let uu____86610 = maybe_eta t2  in
                    (uu____86603, uu____86610)  in
                  (match uu____86586 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3573_86652 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3573_86652.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3573_86652.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3573_86652.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3573_86652.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3573_86652.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3573_86652.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3573_86652.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3573_86652.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____86673 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____86673
                       then
                         let uu____86676 = destruct_flex_t not_abs wl  in
                         (match uu____86676 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_86693 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_86693.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_86693.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_86693.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_86693.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_86693.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_86693.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_86693.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_86693.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____86717 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____86717
                       then
                         let uu____86720 = destruct_flex_t not_abs wl  in
                         (match uu____86720 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_86737 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_86737.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_86737.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_86737.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_86737.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_86737.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_86737.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_86737.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_86737.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____86741 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____86771 =
                    let uu____86776 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____86776 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3613_86804 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3613_86804.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3613_86804.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3615_86806 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3615_86806.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3615_86806.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____86807,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3613_86822 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3613_86822.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3613_86822.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3615_86824 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3615_86824.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3615_86824.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____86825 -> (x1, x2)  in
                  (match uu____86771 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____86844 = as_refinement false env t11  in
                       (match uu____86844 with
                        | (x12,phi11) ->
                            let uu____86852 = as_refinement false env t21  in
                            (match uu____86852 with
                             | (x22,phi21) ->
                                 ((let uu____86861 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____86861
                                   then
                                     ((let uu____86866 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____86868 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____86870 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____86866
                                         uu____86868 uu____86870);
                                      (let uu____86873 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____86875 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____86877 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____86873
                                         uu____86875 uu____86877))
                                   else ());
                                  (let uu____86882 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____86882 with
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
                                         let uu____86953 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____86953
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____86965 =
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
                                         (let uu____86978 =
                                            let uu____86981 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____86981
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____86978
                                            (p_guard base_prob));
                                         (let uu____87000 =
                                            let uu____87003 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____87003
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____87000
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____87022 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____87022)
                                          in
                                       let has_uvars =
                                         (let uu____87027 =
                                            let uu____87029 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____87029
                                             in
                                          Prims.op_Negation uu____87027) ||
                                           (let uu____87033 =
                                              let uu____87035 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____87035
                                               in
                                            Prims.op_Negation uu____87033)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____87039 =
                                           let uu____87044 =
                                             let uu____87053 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____87053]  in
                                           mk_t_problem wl1 uu____87044 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____87039 with
                                          | (ref_prob,wl2) ->
                                              let uu____87075 =
                                                solve env1
                                                  (let uu___3657_87077 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3657_87077.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3657_87077.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3657_87077.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3657_87077.tcenv);
                                                     wl_implicits =
                                                       (uu___3657_87077.wl_implicits)
                                                   })
                                                 in
                                              (match uu____87075 with
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
                                               | Success uu____87094 ->
                                                   let guard =
                                                     let uu____87102 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____87102
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___3668_87111 =
                                                       wl3  in
                                                     {
                                                       attempting =
                                                         (uu___3668_87111.attempting);
                                                       wl_deferred =
                                                         (uu___3668_87111.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            (Prims.parse_int "1"));
                                                       defer_ok =
                                                         (uu___3668_87111.defer_ok);
                                                       smt_ok =
                                                         (uu___3668_87111.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___3668_87111.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___3668_87111.tcenv);
                                                       wl_implicits =
                                                         (uu___3668_87111.wl_implicits)
                                                     }  in
                                                   let uu____87113 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____87113))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____87116,FStar_Syntax_Syntax.Tm_uvar uu____87117) ->
                  let uu____87142 = destruct_flex_t t1 wl  in
                  (match uu____87142 with
                   | (f1,wl1) ->
                       let uu____87149 = destruct_flex_t t2 wl1  in
                       (match uu____87149 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87156;
                    FStar_Syntax_Syntax.pos = uu____87157;
                    FStar_Syntax_Syntax.vars = uu____87158;_},uu____87159),FStar_Syntax_Syntax.Tm_uvar
                 uu____87160) ->
                  let uu____87209 = destruct_flex_t t1 wl  in
                  (match uu____87209 with
                   | (f1,wl1) ->
                       let uu____87216 = destruct_flex_t t2 wl1  in
                       (match uu____87216 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____87223,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87224;
                    FStar_Syntax_Syntax.pos = uu____87225;
                    FStar_Syntax_Syntax.vars = uu____87226;_},uu____87227))
                  ->
                  let uu____87276 = destruct_flex_t t1 wl  in
                  (match uu____87276 with
                   | (f1,wl1) ->
                       let uu____87283 = destruct_flex_t t2 wl1  in
                       (match uu____87283 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87290;
                    FStar_Syntax_Syntax.pos = uu____87291;
                    FStar_Syntax_Syntax.vars = uu____87292;_},uu____87293),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87294;
                    FStar_Syntax_Syntax.pos = uu____87295;
                    FStar_Syntax_Syntax.vars = uu____87296;_},uu____87297))
                  ->
                  let uu____87370 = destruct_flex_t t1 wl  in
                  (match uu____87370 with
                   | (f1,wl1) ->
                       let uu____87377 = destruct_flex_t t2 wl1  in
                       (match uu____87377 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____87384,uu____87385) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____87398 = destruct_flex_t t1 wl  in
                  (match uu____87398 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87405;
                    FStar_Syntax_Syntax.pos = uu____87406;
                    FStar_Syntax_Syntax.vars = uu____87407;_},uu____87408),uu____87409)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____87446 = destruct_flex_t t1 wl  in
                  (match uu____87446 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____87453,FStar_Syntax_Syntax.Tm_uvar uu____87454) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____87467,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87468;
                    FStar_Syntax_Syntax.pos = uu____87469;
                    FStar_Syntax_Syntax.vars = uu____87470;_},uu____87471))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____87508,FStar_Syntax_Syntax.Tm_arrow uu____87509) ->
                  solve_t' env
                    (let uu___3768_87537 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3768_87537.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3768_87537.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3768_87537.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3768_87537.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3768_87537.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3768_87537.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3768_87537.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3768_87537.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3768_87537.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87538;
                    FStar_Syntax_Syntax.pos = uu____87539;
                    FStar_Syntax_Syntax.vars = uu____87540;_},uu____87541),FStar_Syntax_Syntax.Tm_arrow
                 uu____87542) ->
                  solve_t' env
                    (let uu___3768_87594 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3768_87594.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3768_87594.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3768_87594.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3768_87594.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3768_87594.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3768_87594.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3768_87594.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3768_87594.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3768_87594.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____87595,FStar_Syntax_Syntax.Tm_uvar uu____87596) ->
                  let uu____87609 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____87609
              | (uu____87610,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87611;
                    FStar_Syntax_Syntax.pos = uu____87612;
                    FStar_Syntax_Syntax.vars = uu____87613;_},uu____87614))
                  ->
                  let uu____87651 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____87651
              | (FStar_Syntax_Syntax.Tm_uvar uu____87652,uu____87653) ->
                  let uu____87666 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____87666
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87667;
                    FStar_Syntax_Syntax.pos = uu____87668;
                    FStar_Syntax_Syntax.vars = uu____87669;_},uu____87670),uu____87671)
                  ->
                  let uu____87708 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____87708
              | (FStar_Syntax_Syntax.Tm_refine uu____87709,uu____87710) ->
                  let t21 =
                    let uu____87718 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____87718  in
                  solve_t env
                    (let uu___3803_87744 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3803_87744.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3803_87744.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3803_87744.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3803_87744.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3803_87744.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3803_87744.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3803_87744.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3803_87744.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3803_87744.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____87745,FStar_Syntax_Syntax.Tm_refine uu____87746) ->
                  let t11 =
                    let uu____87754 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____87754  in
                  solve_t env
                    (let uu___3810_87780 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3810_87780.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3810_87780.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3810_87780.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3810_87780.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3810_87780.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3810_87780.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3810_87780.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3810_87780.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3810_87780.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____87862 =
                    let uu____87863 = guard_of_prob env wl problem t1 t2  in
                    match uu____87863 with
                    | (guard,wl1) ->
                        let uu____87870 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____87870
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____88089 = br1  in
                        (match uu____88089 with
                         | (p1,w1,uu____88118) ->
                             let uu____88135 = br2  in
                             (match uu____88135 with
                              | (p2,w2,uu____88158) ->
                                  let uu____88163 =
                                    let uu____88165 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____88165  in
                                  if uu____88163
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____88192 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____88192 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____88229 = br2  in
                                         (match uu____88229 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____88262 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____88262
                                                 in
                                              let uu____88267 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____88298,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____88319) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____88378 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____88378 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____88267
                                                (fun uu____88450  ->
                                                   match uu____88450 with
                                                   | (wprobs,wl2) ->
                                                       let uu____88487 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____88487
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____88508
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____88508
                                                              then
                                                                let uu____88513
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____88515
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____88513
                                                                  uu____88515
                                                              else ());
                                                             (let uu____88521
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____88521
                                                                (fun
                                                                   uu____88557
                                                                    ->
                                                                   match uu____88557
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
                    | uu____88686 -> FStar_Pervasives_Native.None  in
                  let uu____88727 = solve_branches wl brs1 brs2  in
                  (match uu____88727 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____88778 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____88778 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____88812 =
                                FStar_List.map
                                  (fun uu____88824  ->
                                     match uu____88824 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____88812  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____88833 =
                              let uu____88834 =
                                let uu____88835 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____88835
                                  (let uu___3909_88843 = wl3  in
                                   {
                                     attempting =
                                       (uu___3909_88843.attempting);
                                     wl_deferred =
                                       (uu___3909_88843.wl_deferred);
                                     ctr = (uu___3909_88843.ctr);
                                     defer_ok = (uu___3909_88843.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3909_88843.umax_heuristic_ok);
                                     tcenv = (uu___3909_88843.tcenv);
                                     wl_implicits =
                                       (uu___3909_88843.wl_implicits)
                                   })
                                 in
                              solve env uu____88834  in
                            (match uu____88833 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____88848 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____88855,uu____88856) ->
                  let head1 =
                    let uu____88880 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____88880
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____88926 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____88926
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____88972 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____88972
                    then
                      let uu____88976 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____88978 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____88980 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____88976 uu____88978 uu____88980
                    else ());
                   (let no_free_uvars t =
                      (let uu____88994 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____88994) &&
                        (let uu____88998 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____88998)
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
                      let uu____89015 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89015 = FStar_Syntax_Util.Equal  in
                    let uu____89016 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89016
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89020 = equal t1 t2  in
                         (if uu____89020
                          then
                            let uu____89023 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89023
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89028 =
                            let uu____89035 = equal t1 t2  in
                            if uu____89035
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89048 = mk_eq2 wl env orig t1 t2  in
                               match uu____89048 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89028 with
                          | (guard,wl1) ->
                              let uu____89069 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89069))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____89072,uu____89073) ->
                  let head1 =
                    let uu____89081 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89081
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89127 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89127
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89173 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89173
                    then
                      let uu____89177 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89179 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89181 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89177 uu____89179 uu____89181
                    else ());
                   (let no_free_uvars t =
                      (let uu____89195 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89195) &&
                        (let uu____89199 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89199)
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
                      let uu____89216 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89216 = FStar_Syntax_Util.Equal  in
                    let uu____89217 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89217
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89221 = equal t1 t2  in
                         (if uu____89221
                          then
                            let uu____89224 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89224
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89229 =
                            let uu____89236 = equal t1 t2  in
                            if uu____89236
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89249 = mk_eq2 wl env orig t1 t2  in
                               match uu____89249 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89229 with
                          | (guard,wl1) ->
                              let uu____89270 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89270))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____89273,uu____89274) ->
                  let head1 =
                    let uu____89276 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89276
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89322 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89322
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89368 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89368
                    then
                      let uu____89372 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89374 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89376 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89372 uu____89374 uu____89376
                    else ());
                   (let no_free_uvars t =
                      (let uu____89390 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89390) &&
                        (let uu____89394 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89394)
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
                      let uu____89411 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89411 = FStar_Syntax_Util.Equal  in
                    let uu____89412 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89412
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89416 = equal t1 t2  in
                         (if uu____89416
                          then
                            let uu____89419 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89419
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89424 =
                            let uu____89431 = equal t1 t2  in
                            if uu____89431
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89444 = mk_eq2 wl env orig t1 t2  in
                               match uu____89444 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89424 with
                          | (guard,wl1) ->
                              let uu____89465 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89465))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____89468,uu____89469) ->
                  let head1 =
                    let uu____89471 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89471
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89517 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89517
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89563 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89563
                    then
                      let uu____89567 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89569 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89571 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89567 uu____89569 uu____89571
                    else ());
                   (let no_free_uvars t =
                      (let uu____89585 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89585) &&
                        (let uu____89589 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89589)
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
                      let uu____89606 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89606 = FStar_Syntax_Util.Equal  in
                    let uu____89607 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89607
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89611 = equal t1 t2  in
                         (if uu____89611
                          then
                            let uu____89614 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89614
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89619 =
                            let uu____89626 = equal t1 t2  in
                            if uu____89626
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89639 = mk_eq2 wl env orig t1 t2  in
                               match uu____89639 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89619 with
                          | (guard,wl1) ->
                              let uu____89660 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89660))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____89663,uu____89664) ->
                  let head1 =
                    let uu____89666 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89666
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89712 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89712
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89758 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89758
                    then
                      let uu____89762 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89764 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89766 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89762 uu____89764 uu____89766
                    else ());
                   (let no_free_uvars t =
                      (let uu____89780 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89780) &&
                        (let uu____89784 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89784)
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
                      let uu____89801 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89801 = FStar_Syntax_Util.Equal  in
                    let uu____89802 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89802
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89806 = equal t1 t2  in
                         (if uu____89806
                          then
                            let uu____89809 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89809
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89814 =
                            let uu____89821 = equal t1 t2  in
                            if uu____89821
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89834 = mk_eq2 wl env orig t1 t2  in
                               match uu____89834 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89814 with
                          | (guard,wl1) ->
                              let uu____89855 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89855))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____89858,uu____89859) ->
                  let head1 =
                    let uu____89877 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89877
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89923 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89923
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89969 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89969
                    then
                      let uu____89973 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89975 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89977 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89973 uu____89975 uu____89977
                    else ());
                   (let no_free_uvars t =
                      (let uu____89991 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89991) &&
                        (let uu____89995 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89995)
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
                      let uu____90012 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90012 = FStar_Syntax_Util.Equal  in
                    let uu____90013 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90013
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90017 = equal t1 t2  in
                         (if uu____90017
                          then
                            let uu____90020 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90020
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90025 =
                            let uu____90032 = equal t1 t2  in
                            if uu____90032
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90045 = mk_eq2 wl env orig t1 t2  in
                               match uu____90045 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90025 with
                          | (guard,wl1) ->
                              let uu____90066 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90066))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90069,FStar_Syntax_Syntax.Tm_match uu____90070) ->
                  let head1 =
                    let uu____90094 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90094
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90140 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90140
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90186 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90186
                    then
                      let uu____90190 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90192 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90194 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90190 uu____90192 uu____90194
                    else ());
                   (let no_free_uvars t =
                      (let uu____90208 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90208) &&
                        (let uu____90212 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90212)
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
                      let uu____90229 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90229 = FStar_Syntax_Util.Equal  in
                    let uu____90230 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90230
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90234 = equal t1 t2  in
                         (if uu____90234
                          then
                            let uu____90237 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90237
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90242 =
                            let uu____90249 = equal t1 t2  in
                            if uu____90249
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90262 = mk_eq2 wl env orig t1 t2  in
                               match uu____90262 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90242 with
                          | (guard,wl1) ->
                              let uu____90283 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90283))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90286,FStar_Syntax_Syntax.Tm_uinst uu____90287) ->
                  let head1 =
                    let uu____90295 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90295
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90335 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90335
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90375 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90375
                    then
                      let uu____90379 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90381 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90383 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90379 uu____90381 uu____90383
                    else ());
                   (let no_free_uvars t =
                      (let uu____90397 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90397) &&
                        (let uu____90401 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90401)
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
                      let uu____90418 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90418 = FStar_Syntax_Util.Equal  in
                    let uu____90419 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90419
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90423 = equal t1 t2  in
                         (if uu____90423
                          then
                            let uu____90426 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90426
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90431 =
                            let uu____90438 = equal t1 t2  in
                            if uu____90438
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90451 = mk_eq2 wl env orig t1 t2  in
                               match uu____90451 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90431 with
                          | (guard,wl1) ->
                              let uu____90472 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90472))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90475,FStar_Syntax_Syntax.Tm_name uu____90476) ->
                  let head1 =
                    let uu____90478 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90478
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90518 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90518
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90558 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90558
                    then
                      let uu____90562 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90564 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90566 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90562 uu____90564 uu____90566
                    else ());
                   (let no_free_uvars t =
                      (let uu____90580 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90580) &&
                        (let uu____90584 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90584)
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
                      let uu____90601 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90601 = FStar_Syntax_Util.Equal  in
                    let uu____90602 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90602
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90606 = equal t1 t2  in
                         (if uu____90606
                          then
                            let uu____90609 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90609
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90614 =
                            let uu____90621 = equal t1 t2  in
                            if uu____90621
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90634 = mk_eq2 wl env orig t1 t2  in
                               match uu____90634 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90614 with
                          | (guard,wl1) ->
                              let uu____90655 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90655))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90658,FStar_Syntax_Syntax.Tm_constant uu____90659) ->
                  let head1 =
                    let uu____90661 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90661
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90701 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90701
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90741 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90741
                    then
                      let uu____90745 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90747 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90749 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90745 uu____90747 uu____90749
                    else ());
                   (let no_free_uvars t =
                      (let uu____90763 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90763) &&
                        (let uu____90767 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90767)
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
                      let uu____90784 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90784 = FStar_Syntax_Util.Equal  in
                    let uu____90785 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90785
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90789 = equal t1 t2  in
                         (if uu____90789
                          then
                            let uu____90792 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90792
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90797 =
                            let uu____90804 = equal t1 t2  in
                            if uu____90804
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90817 = mk_eq2 wl env orig t1 t2  in
                               match uu____90817 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90797 with
                          | (guard,wl1) ->
                              let uu____90838 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90838))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90841,FStar_Syntax_Syntax.Tm_fvar uu____90842) ->
                  let head1 =
                    let uu____90844 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90844
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90884 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90884
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90924 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90924
                    then
                      let uu____90928 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90930 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90932 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90928 uu____90930 uu____90932
                    else ());
                   (let no_free_uvars t =
                      (let uu____90946 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90946) &&
                        (let uu____90950 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90950)
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
                      let uu____90967 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90967 = FStar_Syntax_Util.Equal  in
                    let uu____90968 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90968
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90972 = equal t1 t2  in
                         (if uu____90972
                          then
                            let uu____90975 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90975
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90980 =
                            let uu____90987 = equal t1 t2  in
                            if uu____90987
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____91000 = mk_eq2 wl env orig t1 t2  in
                               match uu____91000 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90980 with
                          | (guard,wl1) ->
                              let uu____91021 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____91021))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____91024,FStar_Syntax_Syntax.Tm_app uu____91025) ->
                  let head1 =
                    let uu____91043 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____91043
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____91083 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____91083
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____91123 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____91123
                    then
                      let uu____91127 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____91129 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____91131 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____91127 uu____91129 uu____91131
                    else ());
                   (let no_free_uvars t =
                      (let uu____91145 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____91145) &&
                        (let uu____91149 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____91149)
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
                      let uu____91166 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____91166 = FStar_Syntax_Util.Equal  in
                    let uu____91167 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____91167
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____91171 = equal t1 t2  in
                         (if uu____91171
                          then
                            let uu____91174 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____91174
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____91179 =
                            let uu____91186 = equal t1 t2  in
                            if uu____91186
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____91199 = mk_eq2 wl env orig t1 t2  in
                               match uu____91199 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____91179 with
                          | (guard,wl1) ->
                              let uu____91220 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____91220))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____91223,FStar_Syntax_Syntax.Tm_let uu____91224) ->
                  let uu____91251 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____91251
                  then
                    let uu____91254 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____91254
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____91258,uu____91259) ->
                  let uu____91273 =
                    let uu____91279 =
                      let uu____91281 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____91283 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____91285 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____91287 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____91281 uu____91283 uu____91285 uu____91287
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____91279)
                     in
                  FStar_Errors.raise_error uu____91273
                    t1.FStar_Syntax_Syntax.pos
              | (uu____91291,FStar_Syntax_Syntax.Tm_let uu____91292) ->
                  let uu____91306 =
                    let uu____91312 =
                      let uu____91314 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____91316 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____91318 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____91320 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____91314 uu____91316 uu____91318 uu____91320
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____91312)
                     in
                  FStar_Errors.raise_error uu____91306
                    t1.FStar_Syntax_Syntax.pos
              | uu____91324 -> giveup env "head tag mismatch" orig))))

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
          (let uu____91388 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____91388
           then
             let uu____91393 =
               let uu____91395 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____91395  in
             let uu____91396 =
               let uu____91398 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____91398  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____91393 uu____91396
           else ());
          (let uu____91402 =
             let uu____91404 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____91404  in
           if uu____91402
           then
             let uu____91407 =
               let uu____91409 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____91411 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____91409 uu____91411
                in
             giveup env uu____91407 orig
           else
             (let uu____91416 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____91416 with
              | (ret_sub_prob,wl1) ->
                  let uu____91424 =
                    FStar_List.fold_right2
                      (fun uu____91461  ->
                         fun uu____91462  ->
                           fun uu____91463  ->
                             match (uu____91461, uu____91462, uu____91463)
                             with
                             | ((a1,uu____91507),(a2,uu____91509),(arg_sub_probs,wl2))
                                 ->
                                 let uu____91542 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____91542 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____91424 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____91572 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____91572  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____91580 = attempt sub_probs wl3  in
                       solve env uu____91580)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____91603 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____91606)::[] -> wp1
              | uu____91631 ->
                  let uu____91642 =
                    let uu____91644 =
                      let uu____91646 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____91646  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____91644
                     in
                  failwith uu____91642
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____91653 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____91653]
              | x -> x  in
            let uu____91655 =
              let uu____91666 =
                let uu____91675 =
                  let uu____91676 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____91676 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____91675  in
              [uu____91666]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____91655;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____91694 = lift_c1 ()  in solve_eq uu____91694 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___616_91703  ->
                       match uu___616_91703 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____91708 -> false))
                in
             let uu____91710 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____91740)::uu____91741,(wp2,uu____91743)::uu____91744)
                   -> (wp1, wp2)
               | uu____91817 ->
                   let uu____91842 =
                     let uu____91848 =
                       let uu____91850 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____91852 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____91850 uu____91852
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____91848)
                      in
                   FStar_Errors.raise_error uu____91842
                     env.FStar_TypeChecker_Env.range
                in
             match uu____91710 with
             | (wpc1,wpc2) ->
                 let uu____91862 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____91862
                 then
                   let uu____91867 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____91867 wl
                 else
                   (let uu____91871 =
                      let uu____91878 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____91878  in
                    match uu____91871 with
                    | (c2_decl,qualifiers) ->
                        let uu____91899 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____91899
                        then
                          let c1_repr =
                            let uu____91906 =
                              let uu____91907 =
                                let uu____91908 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____91908  in
                              let uu____91909 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____91907 uu____91909
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____91906
                             in
                          let c2_repr =
                            let uu____91911 =
                              let uu____91912 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____91913 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____91912 uu____91913
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____91911
                             in
                          let uu____91914 =
                            let uu____91919 =
                              let uu____91921 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____91923 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____91921 uu____91923
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____91919
                             in
                          (match uu____91914 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____91929 = attempt [prob] wl2  in
                               solve env uu____91929)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____91944 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____91944
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____91953 =
                                     let uu____91960 =
                                       let uu____91961 =
                                         let uu____91978 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____91981 =
                                           let uu____91992 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____92001 =
                                             let uu____92012 =
                                               let uu____92021 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____92021
                                                in
                                             [uu____92012]  in
                                           uu____91992 :: uu____92001  in
                                         (uu____91978, uu____91981)  in
                                       FStar_Syntax_Syntax.Tm_app uu____91961
                                        in
                                     FStar_Syntax_Syntax.mk uu____91960  in
                                   uu____91953 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____92073 =
                                    let uu____92080 =
                                      let uu____92081 =
                                        let uu____92098 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____92101 =
                                          let uu____92112 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____92121 =
                                            let uu____92132 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____92141 =
                                              let uu____92152 =
                                                let uu____92161 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____92161
                                                 in
                                              [uu____92152]  in
                                            uu____92132 :: uu____92141  in
                                          uu____92112 :: uu____92121  in
                                        (uu____92098, uu____92101)  in
                                      FStar_Syntax_Syntax.Tm_app uu____92081
                                       in
                                    FStar_Syntax_Syntax.mk uu____92080  in
                                  uu____92073 FStar_Pervasives_Native.None r)
                              in
                           (let uu____92218 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____92218
                            then
                              let uu____92223 =
                                let uu____92225 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____92225
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____92223
                            else ());
                           (let uu____92229 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____92229 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____92238 =
                                    let uu____92241 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _92244  ->
                                         FStar_Pervasives_Native.Some _92244)
                                      uu____92241
                                     in
                                  solve_prob orig uu____92238 [] wl1  in
                                let uu____92245 = attempt [base_prob] wl2  in
                                solve env uu____92245))))
           in
        let uu____92246 = FStar_Util.physical_equality c1 c2  in
        if uu____92246
        then
          let uu____92249 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____92249
        else
          ((let uu____92253 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____92253
            then
              let uu____92258 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____92260 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____92258
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____92260
            else ());
           (let uu____92265 =
              let uu____92274 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____92277 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____92274, uu____92277)  in
            match uu____92265 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____92295),FStar_Syntax_Syntax.Total
                    (t2,uu____92297)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____92314 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____92314 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____92316,FStar_Syntax_Syntax.Total uu____92317) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____92336),FStar_Syntax_Syntax.Total
                    (t2,uu____92338)) ->
                     let uu____92355 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____92355 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____92358),FStar_Syntax_Syntax.GTotal
                    (t2,uu____92360)) ->
                     let uu____92377 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____92377 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____92380),FStar_Syntax_Syntax.GTotal
                    (t2,uu____92382)) ->
                     let uu____92399 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____92399 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____92401,FStar_Syntax_Syntax.Comp uu____92402) ->
                     let uu____92411 =
                       let uu___4158_92414 = problem  in
                       let uu____92417 =
                         let uu____92418 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____92418
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4158_92414.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____92417;
                         FStar_TypeChecker_Common.relation =
                           (uu___4158_92414.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___4158_92414.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___4158_92414.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4158_92414.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4158_92414.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4158_92414.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4158_92414.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4158_92414.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____92411 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____92419,FStar_Syntax_Syntax.Comp uu____92420) ->
                     let uu____92429 =
                       let uu___4158_92432 = problem  in
                       let uu____92435 =
                         let uu____92436 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____92436
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4158_92432.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____92435;
                         FStar_TypeChecker_Common.relation =
                           (uu___4158_92432.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___4158_92432.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___4158_92432.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4158_92432.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4158_92432.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4158_92432.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4158_92432.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4158_92432.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____92429 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____92437,FStar_Syntax_Syntax.GTotal uu____92438) ->
                     let uu____92447 =
                       let uu___4170_92450 = problem  in
                       let uu____92453 =
                         let uu____92454 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____92454
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4170_92450.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___4170_92450.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___4170_92450.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____92453;
                         FStar_TypeChecker_Common.element =
                           (uu___4170_92450.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4170_92450.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4170_92450.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4170_92450.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4170_92450.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4170_92450.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____92447 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____92455,FStar_Syntax_Syntax.Total uu____92456) ->
                     let uu____92465 =
                       let uu___4170_92468 = problem  in
                       let uu____92471 =
                         let uu____92472 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____92472
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4170_92468.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___4170_92468.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___4170_92468.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____92471;
                         FStar_TypeChecker_Common.element =
                           (uu___4170_92468.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4170_92468.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4170_92468.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4170_92468.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4170_92468.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4170_92468.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____92465 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____92473,FStar_Syntax_Syntax.Comp uu____92474) ->
                     let uu____92475 =
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
                     if uu____92475
                     then
                       let uu____92478 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____92478 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____92485 =
                            let uu____92490 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____92490
                            then (c1_comp, c2_comp)
                            else
                              (let uu____92499 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____92500 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____92499, uu____92500))
                             in
                          match uu____92485 with
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
                           (let uu____92508 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____92508
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____92516 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____92516 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____92519 =
                                  let uu____92521 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____92523 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____92521 uu____92523
                                   in
                                giveup env uu____92519 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____92534 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____92534 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____92584 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____92584 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____92609 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____92640  ->
                match uu____92640 with
                | (u1,u2) ->
                    let uu____92648 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____92650 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____92648 uu____92650))
         in
      FStar_All.pipe_right uu____92609 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____92687,[])) when
          let uu____92714 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____92714 -> "{}"
      | uu____92717 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____92744 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____92744
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____92756 =
              FStar_List.map
                (fun uu____92769  ->
                   match uu____92769 with
                   | (uu____92776,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____92756 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____92787 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____92787 imps
  
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
                  let uu____92844 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____92844
                  then
                    let uu____92852 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____92854 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____92852
                      (rel_to_string rel) uu____92854
                  else "TOP"  in
                let uu____92860 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____92860 with
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
              let uu____92920 =
                let uu____92923 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _92926  -> FStar_Pervasives_Native.Some _92926)
                  uu____92923
                 in
              FStar_Syntax_Syntax.new_bv uu____92920 t1  in
            let uu____92927 =
              let uu____92932 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____92932
               in
            match uu____92927 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____92992 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____92992
         then
           let uu____92997 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____92997
         else ());
        (let uu____93004 =
           FStar_Util.record_time (fun uu____93011  -> solve env probs)  in
         match uu____93004 with
         | (sol,ms) ->
             ((let uu____93023 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____93023
               then
                 let uu____93028 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____93028
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____93041 =
                     FStar_Util.record_time
                       (fun uu____93048  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____93041 with
                    | ((),ms1) ->
                        ((let uu____93059 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____93059
                          then
                            let uu____93064 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____93064
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____93078 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____93078
                     then
                       let uu____93085 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____93085
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
          ((let uu____93112 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____93112
            then
              let uu____93117 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____93117
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____93124 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____93124
             then
               let uu____93129 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____93129
             else ());
            (let f2 =
               let uu____93135 =
                 let uu____93136 = FStar_Syntax_Util.unmeta f1  in
                 uu____93136.FStar_Syntax_Syntax.n  in
               match uu____93135 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____93140 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___4286_93141 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___4286_93141.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___4286_93141.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___4286_93141.FStar_TypeChecker_Env.implicits)
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
            let uu____93196 =
              let uu____93197 =
                let uu____93198 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _93199  ->
                       FStar_TypeChecker_Common.NonTrivial _93199)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____93198;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____93197  in
            FStar_All.pipe_left
              (fun _93206  -> FStar_Pervasives_Native.Some _93206)
              uu____93196
  
let with_guard_no_simp :
  'Auu____93216 .
    'Auu____93216 ->
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
            let uu____93239 =
              let uu____93240 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _93241  -> FStar_TypeChecker_Common.NonTrivial _93241)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____93240;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____93239
  
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
          (let uu____93274 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____93274
           then
             let uu____93279 = FStar_Syntax_Print.term_to_string t1  in
             let uu____93281 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____93279
               uu____93281
           else ());
          (let uu____93286 =
             let uu____93291 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____93291
              in
           match uu____93286 with
           | (prob,wl) ->
               let g =
                 let uu____93299 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____93309  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____93299  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____93345 = try_teq true env t1 t2  in
        match uu____93345 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____93350 = FStar_TypeChecker_Env.get_range env  in
              let uu____93351 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____93350 uu____93351);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____93359 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____93359
              then
                let uu____93364 = FStar_Syntax_Print.term_to_string t1  in
                let uu____93366 = FStar_Syntax_Print.term_to_string t2  in
                let uu____93368 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____93364
                  uu____93366 uu____93368
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
          let uu____93394 = FStar_TypeChecker_Env.get_range env  in
          let uu____93395 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____93394 uu____93395
  
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
        (let uu____93424 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____93424
         then
           let uu____93429 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____93431 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____93429 uu____93431
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____93442 =
           let uu____93449 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____93449 "sub_comp"
            in
         match uu____93442 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____93462 =
                 FStar_Util.record_time
                   (fun uu____93474  ->
                      let uu____93475 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____93486  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____93475)
                  in
               match uu____93462 with
               | (r,ms) ->
                   ((let uu____93517 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____93517
                     then
                       let uu____93522 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____93524 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____93526 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____93522 uu____93524
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____93526
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
      fun uu____93564  ->
        match uu____93564 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____93607 =
                 let uu____93613 =
                   let uu____93615 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____93617 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____93615 uu____93617
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____93613)  in
               let uu____93621 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____93607 uu____93621)
               in
            let equiv1 v1 v' =
              let uu____93634 =
                let uu____93639 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____93640 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____93639, uu____93640)  in
              match uu____93634 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____93660 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____93691 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____93691 with
                      | FStar_Syntax_Syntax.U_unif uu____93698 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____93727  ->
                                    match uu____93727 with
                                    | (u,v') ->
                                        let uu____93736 = equiv1 v1 v'  in
                                        if uu____93736
                                        then
                                          let uu____93741 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____93741 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____93762 -> []))
               in
            let uu____93767 =
              let wl =
                let uu___4377_93771 = empty_worklist env  in
                {
                  attempting = (uu___4377_93771.attempting);
                  wl_deferred = (uu___4377_93771.wl_deferred);
                  ctr = (uu___4377_93771.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4377_93771.smt_ok);
                  umax_heuristic_ok = (uu___4377_93771.umax_heuristic_ok);
                  tcenv = (uu___4377_93771.tcenv);
                  wl_implicits = (uu___4377_93771.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____93790  ->
                      match uu____93790 with
                      | (lb,v1) ->
                          let uu____93797 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____93797 with
                           | USolved wl1 -> ()
                           | uu____93800 -> fail1 lb v1)))
               in
            let rec check_ineq uu____93811 =
              match uu____93811 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____93823) -> true
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
                      uu____93847,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____93849,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____93860) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____93868,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____93877 -> false)
               in
            let uu____93883 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____93900  ->
                      match uu____93900 with
                      | (u,v1) ->
                          let uu____93908 = check_ineq (u, v1)  in
                          if uu____93908
                          then true
                          else
                            ((let uu____93916 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____93916
                              then
                                let uu____93921 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____93923 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____93921
                                  uu____93923
                              else ());
                             false)))
               in
            if uu____93883
            then ()
            else
              ((let uu____93933 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____93933
                then
                  ((let uu____93939 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____93939);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____93951 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____93951))
                else ());
               (let uu____93964 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____93964))
  
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
        let fail1 uu____94038 =
          match uu____94038 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4454_94064 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___4454_94064.attempting);
            wl_deferred = (uu___4454_94064.wl_deferred);
            ctr = (uu___4454_94064.ctr);
            defer_ok;
            smt_ok = (uu___4454_94064.smt_ok);
            umax_heuristic_ok = (uu___4454_94064.umax_heuristic_ok);
            tcenv = (uu___4454_94064.tcenv);
            wl_implicits = (uu___4454_94064.wl_implicits)
          }  in
        (let uu____94067 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____94067
         then
           let uu____94072 = FStar_Util.string_of_bool defer_ok  in
           let uu____94074 = wl_to_string wl  in
           let uu____94076 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____94072 uu____94074 uu____94076
         else ());
        (let g1 =
           let uu____94082 = solve_and_commit env wl fail1  in
           match uu____94082 with
           | FStar_Pervasives_Native.Some
               (uu____94089::uu____94090,uu____94091) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4469_94120 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___4469_94120.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___4469_94120.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____94121 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___4474_94130 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4474_94130.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4474_94130.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___4474_94130.FStar_TypeChecker_Env.implicits)
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
    let uu____94184 = FStar_ST.op_Bang last_proof_ns  in
    match uu____94184 with
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
            let uu___4493_94309 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___4493_94309.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___4493_94309.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___4493_94309.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____94310 =
            let uu____94312 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____94312  in
          if uu____94310
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____94324 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____94325 =
                       let uu____94327 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____94327
                        in
                     FStar_Errors.diag uu____94324 uu____94325)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____94335 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____94336 =
                        let uu____94338 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____94338
                         in
                      FStar_Errors.diag uu____94335 uu____94336)
                   else ();
                   (let uu____94344 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____94344
                      "discharge_guard'" env vc1);
                   (let uu____94346 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____94346 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____94355 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____94356 =
                                let uu____94358 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____94358
                                 in
                              FStar_Errors.diag uu____94355 uu____94356)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____94368 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____94369 =
                                let uu____94371 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____94371
                                 in
                              FStar_Errors.diag uu____94368 uu____94369)
                           else ();
                           (let vcs =
                              let uu____94385 = FStar_Options.use_tactics ()
                                 in
                              if uu____94385
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____94407  ->
                                     (let uu____94409 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____94409);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____94453  ->
                                              match uu____94453 with
                                              | (env1,goal,opts) ->
                                                  let uu____94469 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____94469, opts)))))
                              else
                                (let uu____94472 =
                                   let uu____94479 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____94479)  in
                                 [uu____94472])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____94512  ->
                                    match uu____94512 with
                                    | (env1,goal,opts) ->
                                        let uu____94522 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____94522 with
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
                                                (let uu____94534 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____94535 =
                                                   let uu____94537 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____94539 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____94537 uu____94539
                                                    in
                                                 FStar_Errors.diag
                                                   uu____94534 uu____94535)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____94546 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____94547 =
                                                   let uu____94549 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____94549
                                                    in
                                                 FStar_Errors.diag
                                                   uu____94546 uu____94547)
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
      let uu____94567 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____94567 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____94576 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____94576
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____94590 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____94590 with
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
        let uu____94620 = try_teq false env t1 t2  in
        match uu____94620 with
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
            let uu____94664 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____94664 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____94677 ->
                     let uu____94690 =
                       let uu____94691 = FStar_Syntax_Subst.compress r  in
                       uu____94691.FStar_Syntax_Syntax.n  in
                     (match uu____94690 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____94696) ->
                          unresolved ctx_u'
                      | uu____94713 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____94737 = acc  in
            match uu____94737 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____94756 = hd1  in
                     (match uu____94756 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____94767 = unresolved ctx_u  in
                             if uu____94767
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____94791 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____94791
                                     then
                                       let uu____94795 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____94795
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____94804 = teq_nosmt env1 t tm
                                          in
                                       match uu____94804 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Env.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4606_94814 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4606_94814.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4606_94814.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4606_94814.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4606_94814.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4606_94814.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4606_94814.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4606_94814.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4609_94822 = hd1  in
                                       {
                                         FStar_TypeChecker_Env.imp_reason =
                                           (uu___4609_94822.FStar_TypeChecker_Env.imp_reason);
                                         FStar_TypeChecker_Env.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Env.imp_tm =
                                           (uu___4609_94822.FStar_TypeChecker_Env.imp_tm);
                                         FStar_TypeChecker_Env.imp_range =
                                           (uu___4609_94822.FStar_TypeChecker_Env.imp_range)
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
                                    let uu___4613_94833 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4613_94833.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4613_94833.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4613_94833.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4613_94833.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4613_94833.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4613_94833.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4613_94833.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4613_94833.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4613_94833.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___4613_94833.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4613_94833.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4613_94833.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4613_94833.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4613_94833.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4613_94833.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4613_94833.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4613_94833.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4613_94833.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4613_94833.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4613_94833.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4613_94833.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4613_94833.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4613_94833.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4613_94833.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4613_94833.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4613_94833.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4613_94833.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4613_94833.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4613_94833.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4613_94833.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4613_94833.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4613_94833.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4613_94833.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4613_94833.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4613_94833.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4613_94833.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4613_94833.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4613_94833.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4613_94833.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4613_94833.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4613_94833.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4613_94833.FStar_TypeChecker_Env.nbe)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4618_94837 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4618_94837.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4618_94837.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4618_94837.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4618_94837.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4618_94837.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4618_94837.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4618_94837.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4618_94837.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4618_94837.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4618_94837.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___4618_94837.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4618_94837.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4618_94837.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4618_94837.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4618_94837.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4618_94837.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4618_94837.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4618_94837.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4618_94837.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4618_94837.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4618_94837.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4618_94837.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4618_94837.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4618_94837.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4618_94837.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4618_94837.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4618_94837.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4618_94837.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4618_94837.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4618_94837.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4618_94837.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4618_94837.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4618_94837.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4618_94837.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4618_94837.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4618_94837.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4618_94837.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4618_94837.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4618_94837.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4618_94837.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4618_94837.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4618_94837.FStar_TypeChecker_Env.nbe)
                                      }
                                    else env1  in
                                  (let uu____94842 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____94842
                                   then
                                     let uu____94847 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____94849 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____94851 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____94853 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____94847 uu____94849 uu____94851
                                       reason uu____94853
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4624_94860  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____94867 =
                                             let uu____94877 =
                                               let uu____94885 =
                                                 let uu____94887 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____94889 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____94891 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____94887 uu____94889
                                                   uu____94891
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____94885, r)
                                                in
                                             [uu____94877]  in
                                           FStar_Errors.add_errors
                                             uu____94867);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___4632_94911 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___4632_94911.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___4632_94911.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___4632_94911.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____94915 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____94926  ->
                                               let uu____94927 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____94929 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____94931 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____94927 uu____94929
                                                 reason uu____94931)) env2 g2
                                         true
                                        in
                                     match uu____94915 with
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
          let uu___4640_94939 = g  in
          let uu____94940 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4640_94939.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4640_94939.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___4640_94939.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____94940
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
        let uu____94983 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____94983 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____94984 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____94984
      | imp::uu____94986 ->
          let uu____94989 =
            let uu____94995 =
              let uu____94997 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____94999 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____94997 uu____94999 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____94995)
             in
          FStar_Errors.raise_error uu____94989
            imp.FStar_TypeChecker_Env.imp_range
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____95021 = teq_nosmt env t1 t2  in
        match uu____95021 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4662_95040 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___4662_95040.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___4662_95040.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___4662_95040.FStar_TypeChecker_Env.implicits)
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
        (let uu____95076 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____95076
         then
           let uu____95081 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____95083 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____95081
             uu____95083
         else ());
        (let uu____95088 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____95088 with
         | (prob,x,wl) ->
             let g =
               let uu____95107 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____95118  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____95107  in
             ((let uu____95139 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____95139
               then
                 let uu____95144 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____95146 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____95148 =
                   let uu____95150 = FStar_Util.must g  in
                   guard_to_string env uu____95150  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____95144 uu____95146 uu____95148
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
        let uu____95187 = check_subtyping env t1 t2  in
        match uu____95187 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____95206 =
              let uu____95207 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____95207 g  in
            FStar_Pervasives_Native.Some uu____95206
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____95226 = check_subtyping env t1 t2  in
        match uu____95226 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____95245 =
              let uu____95246 =
                let uu____95247 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____95247]  in
              FStar_TypeChecker_Env.close_guard env uu____95246 g  in
            FStar_Pervasives_Native.Some uu____95245
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____95285 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____95285
         then
           let uu____95290 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____95292 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____95290
             uu____95292
         else ());
        (let uu____95297 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____95297 with
         | (prob,x,wl) ->
             let g =
               let uu____95312 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____95323  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____95312  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____95347 =
                      let uu____95348 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____95348]  in
                    FStar_TypeChecker_Env.close_guard env uu____95347 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____95389 = subtype_nosmt env t1 t2  in
        match uu____95389 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  